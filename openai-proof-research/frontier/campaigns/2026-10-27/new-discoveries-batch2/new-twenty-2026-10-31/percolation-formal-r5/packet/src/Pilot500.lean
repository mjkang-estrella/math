import Inputs047
namespace Percolation.Replay
namespace P500
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_14704 : CNF.NClause := [(66,true),(6,false),(21,false),(25,false),(11,false),(16,false)]
theorem der_14704 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14704 :=
  CNF.rup_sound cl_14704 [cl_257,cl_258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_257 v h) (hints_cons _ _ _ (inp_258 v h) (by intro d hd; cases hd)))
def cl_14706 : CNF.NClause := [(71,true),(7,false),(20,false),(26,false),(13,false),(19,false)]
theorem der_14706 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14706 :=
  CNF.rup_sound cl_14706 [cl_577,cl_578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_577 v h) (hints_cons _ _ _ (inp_578 v h) (by intro d hd; cases hd)))
def cl_14708 : CNF.NClause := [(76,true),(8,false),(24,false),(27,false),(10,false),(17,false)]
theorem der_14708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14708 :=
  CNF.rup_sound cl_14708 [cl_897,cl_898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_897 v h) (hints_cons _ _ _ (inp_898 v h) (by intro d hd; cases hd)))
def cl_14710 : CNF.NClause := [(81,true),(9,false),(23,false),(28,false),(12,false),(15,false)]
theorem der_14710 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14710 :=
  CNF.rup_sound cl_14710 [cl_1217,cl_1218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1217 v h) (hints_cons _ _ _ (inp_1218 v h) (by intro d hd; cases hd)))
def cl_14712 : CNF.NClause := [(86,true),(5,false),(22,false),(29,false),(14,false),(18,false)]
theorem der_14712 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14712 :=
  CNF.rup_sound cl_14712 [cl_1537,cl_1538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1537 v h) (hints_cons _ _ _ (inp_1538 v h) (by intro d hd; cases hd)))
def cl_14713 : CNF.NClause := [(1,true),(87,true),(30,false),(2,true),(3,false),(4,false)]
theorem der_14713 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14713 :=
  CNF.rup_sound cl_14713 [cl_1607,cl_1608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1607 v h) (hints_cons _ _ _ (inp_1608 v h) (by intro d hd; cases hd)))
def cl_14714 : CNF.NClause := [(1,false),(87,true),(30,false),(2,true),(3,false),(4,false)]
theorem der_14714 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14714 :=
  CNF.rup_sound cl_14714 [cl_1605,cl_1606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1605 v h) (hints_cons _ _ _ (inp_1606 v h) (by intro d hd; cases hd)))
def cl_14715 : CNF.NClause := [(87,true),(2,true),(30,false),(4,false),(3,false)]
theorem der_14715 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14715 :=
  CNF.rup_sound cl_14715 [cl_14713,cl_14714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14713 v h) (hints_cons _ _ _ (der_14714 v h) (by intro d hd; cases hd)))
def cl_14716 : CNF.NClause := [(88,true),(9,false),(21,false),(29,false),(13,false),(17,false)]
theorem der_14716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14716 :=
  CNF.rup_sound cl_14716 [cl_1665,cl_1666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1665 v h) (hints_cons _ _ _ (inp_1666 v h) (by intro d hd; cases hd)))
def cl_14717 : CNF.NClause := [(89,true),(7,false),(23,false),(27,false),(14,false),(16,false)]
theorem der_14717 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14717 :=
  CNF.rup_sound cl_14717 [cl_1729,cl_1730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1729 v h) (hints_cons _ _ _ (inp_1730 v h) (by intro d hd; cases hd)))
def cl_14718 : CNF.NClause := [(90,true),(8,false),(22,false),(28,false),(11,false),(19,false)]
theorem der_14718 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14718 :=
  CNF.rup_sound cl_14718 [cl_1793,cl_1794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1793 v h) (hints_cons _ _ _ (inp_1794 v h) (by intro d hd; cases hd)))
def cl_14719 : CNF.NClause := [(91,true),(6,false),(24,false),(26,false),(12,false),(18,false)]
theorem der_14719 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14719 :=
  CNF.rup_sound cl_14719 [cl_1857,cl_1858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1857 v h) (hints_cons _ _ _ (inp_1858 v h) (by intro d hd; cases hd)))
def cl_14720 : CNF.NClause := [(92,true),(5,false),(20,false),(25,false),(10,false),(15,false)]
theorem der_14720 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14720 :=
  CNF.rup_sound cl_14720 [cl_1921,cl_1922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1921 v h) (hints_cons _ _ _ (inp_1922 v h) (by intro d hd; cases hd)))
def cl_14721 : CNF.NClause := [(31,true),(61,false),(118,true),(33,true),(34,false),(35,false)]
theorem der_14721 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14721 :=
  CNF.rup_sound cl_14721 [cl_3590,cl_3592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3590 v h) (hints_cons _ _ _ (inp_3592 v h) (by intro d hd; cases hd)))
def cl_14722 : CNF.NClause := [(31,false),(61,false),(118,true),(33,true),(34,false),(35,false)]
theorem der_14722 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14722 :=
  CNF.rup_sound cl_14722 [cl_3589,cl_3591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3589 v h) (hints_cons _ _ _ (inp_3591 v h) (by intro d hd; cases hd)))
def cl_14723 : CNF.NClause := [(61,false),(35,false),(118,true),(33,true),(34,false)]
theorem der_14723 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14723 :=
  CNF.rup_sound cl_14723 [cl_14721,cl_14722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14721 v h) (hints_cons _ _ _ (der_14722 v h) (by intro d hd; cases hd)))
def cl_14730 : CNF.NClause := [(217,true),(225,true),(219,true),(230,false),(234,true),(235,true),(236,true),(237,true),(238,true),(239,true),(244,true),(245,true),(246,true)]
theorem der_14730 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14730 :=
  CNF.rup_sound cl_14730 [cl_8685,cl_8697,cl_8572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8685 v h) (hints_cons _ _ _ (inp_8697 v h) (hints_cons _ _ _ (inp_8572 v h) (by intro d hd; cases hd))))
def cl_14814 : CNF.NClause := [(66,true),(6,true),(25,false),(11,false),(16,false),(21,false)]
theorem der_14814 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14814 :=
  CNF.rup_sound cl_14814 [cl_259,cl_260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_259 v h) (hints_cons _ _ _ (inp_260 v h) (by intro d hd; cases hd)))
def cl_14831 : CNF.NClause := [(118,true),(61,false),(31,false),(33,true),(34,false),(35,true)]
theorem der_14831 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14831 :=
  CNF.rup_sound cl_14831 [cl_3605,cl_3607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3605 v h) (hints_cons _ _ _ (inp_3607 v h) (by intro d hd; cases hd)))
def cl_14833 : CNF.NClause := [(87,true),(0,false),(2,true),(30,false),(3,false),(4,true)]
theorem der_14833 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14833 :=
  CNF.rup_sound cl_14833 [cl_1621,cl_1623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1621 v h) (hints_cons _ _ _ (inp_1623 v h) (by intro d hd; cases hd)))
def cl_14836 : CNF.NClause := [(87,true),(3,false),(2,true),(30,false),(0,true),(4,true)]
theorem der_14836 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14836 :=
  CNF.rup_sound cl_14836 [cl_1624,cl_1622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1624 v h) (hints_cons _ _ _ (inp_1622 v h) (by intro d hd; cases hd)))
def cl_14837 : CNF.NClause := [(118,true),(61,false),(31,true),(33,true),(34,false),(35,true)]
theorem der_14837 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14837 :=
  CNF.rup_sound cl_14837 [cl_3606,cl_3608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3606 v h) (hints_cons _ _ _ (inp_3608 v h) (by intro d hd; cases hd)))
def cl_14841 : CNF.NClause := [(31,false),(118,true),(61,false),(33,true),(34,true),(35,true)]
theorem der_14841 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14841 :=
  CNF.rup_sound cl_14841 [cl_3613,cl_3615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3613 v h) (hints_cons _ _ _ (inp_3615 v h) (by intro d hd; cases hd)))
def cl_14844 : CNF.NClause := [(91,true),(6,true),(26,false),(12,false),(18,false),(24,false)]
theorem der_14844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14844 :=
  CNF.rup_sound cl_14844 [cl_1859,cl_1860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1859 v h) (hints_cons _ _ _ (inp_1860 v h) (by intro d hd; cases hd)))
def cl_14845 : CNF.NClause := [(31,false),(0,true),(92,false),(88,false),(89,false),(90,false),(91,false)]
theorem der_14845 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14845 :=
  CNF.rup_sound cl_14845 [cl_3972,cl_3970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3972 v h) (hints_cons _ _ _ (inp_3970 v h) (by intro d hd; cases hd)))
def cl_14848 : CNF.NClause := [(4,false),(87,true),(0,true),(3,true),(30,false),(2,true)]
theorem der_14848 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14848 :=
  CNF.rup_sound cl_14848 [cl_1614,cl_1616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1614 v h) (hints_cons _ _ _ (inp_1616 v h) (by intro d hd; cases hd)))
def cl_14852 : CNF.NClause := [(35,false),(118,true),(61,false),(33,true),(34,true),(31,true)]
theorem der_14852 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14852 :=
  CNF.rup_sound cl_14852 [cl_3598,cl_3600] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3598 v h) (hints_cons _ _ _ (inp_3600 v h) (by intro d hd; cases hd)))
def cl_14854 : CNF.NClause := [(118,true),(34,true),(61,false),(31,true),(33,false),(35,false)]
theorem der_14854 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14854 :=
  CNF.rup_sound cl_14854 [cl_3594,cl_3596] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3594 v h) (hints_cons _ _ _ (inp_3596 v h) (by intro d hd; cases hd)))
def cl_14862 : CNF.NClause := [(118,true),(34,false),(61,false),(31,true),(33,false),(35,true)]
theorem der_14862 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14862 :=
  CNF.rup_sound cl_14862 [cl_3602,cl_3604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3602 v h) (hints_cons _ _ _ (inp_3604 v h) (by intro d hd; cases hd)))
def cl_14864 : CNF.NClause := [(118,true),(61,false),(34,true),(31,true),(33,false),(35,true)]
theorem der_14864 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14864 :=
  CNF.rup_sound cl_14864 [cl_3610,cl_3612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3610 v h) (hints_cons _ _ _ (inp_3612 v h) (by intro d hd; cases hd)))
def cl_14867 : CNF.NClause := [(4,true),(3,true),(30,false),(2,false),(87,true),(0,true)]
theorem der_14867 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14867 :=
  CNF.rup_sound cl_14867 [cl_1626,cl_1628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1626 v h) (hints_cons _ _ _ (inp_1628 v h) (by intro d hd; cases hd)))
def cl_14868 : CNF.NClause := [(4,false),(3,true),(30,false),(2,false),(87,true),(0,true)]
theorem der_14868 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14868 :=
  CNF.rup_sound cl_14868 [cl_1610,cl_1612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1610 v h) (hints_cons _ _ _ (inp_1612 v h) (by intro d hd; cases hd)))
def cl_14869 : CNF.NClause := [(3,true),(0,true),(30,false),(2,false),(87,true)]
theorem der_14869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14869 :=
  CNF.rup_sound cl_14869 [cl_14867,cl_14868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14867 v h) (hints_cons _ _ _ (der_14868 v h) (by intro d hd; cases hd)))
def cl_14870 : CNF.NClause := [(4,false),(3,false),(30,false),(2,false),(0,true),(87,true)]
theorem der_14870 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14870 :=
  CNF.rup_sound cl_14870 [cl_1602,cl_1604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1602 v h) (hints_cons _ _ _ (inp_1604 v h) (by intro d hd; cases hd)))
def cl_14871 : CNF.NClause := [(4,true),(87,true),(30,false),(2,false),(0,true),(3,false)]
theorem der_14871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14871 :=
  CNF.rup_sound cl_14871 [cl_1620,cl_1618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1620 v h) (hints_cons _ _ _ (inp_1618 v h) (by intro d hd; cases hd)))
def cl_14872 : CNF.NClause := [(3,false),(87,true),(30,false),(2,false),(0,true)]
theorem der_14872 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14872 :=
  CNF.rup_sound cl_14872 [cl_14870,cl_14871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14870 v h) (hints_cons _ _ _ (der_14871 v h) (by intro d hd; cases hd)))
def cl_14873 : CNF.NClause := [(0,true),(87,true),(30,false),(2,false)]
theorem der_14873 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14873 :=
  CNF.rup_sound cl_14873 [cl_14869,cl_14872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14869 v h) (hints_cons _ _ _ (der_14872 v h) (by intro d hd; cases hd)))
def cl_14875 : CNF.NClause := [(4,true),(3,false),(30,false),(2,false),(87,true),(0,false)]
theorem der_14875 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14875 :=
  CNF.rup_sound cl_14875 [cl_1617,cl_1619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1617 v h) (hints_cons _ _ _ (inp_1619 v h) (by intro d hd; cases hd)))
def cl_14877 : CNF.NClause := [(4,true),(2,false),(30,false),(87,true),(3,true),(0,false)]
theorem der_14877 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14877 :=
  CNF.rup_sound cl_14877 [cl_1625,cl_1627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1625 v h) (hints_cons _ _ _ (inp_1627 v h) (by intro d hd; cases hd)))
def cl_14878 : CNF.NClause := [(4,false),(2,false),(30,false),(0,false),(87,true),(3,true)]
theorem der_14878 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14878 :=
  CNF.rup_sound cl_14878 [cl_1609,cl_1611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1609 v h) (hints_cons _ _ _ (inp_1611 v h) (by intro d hd; cases hd)))
def cl_14879 : CNF.NClause := [(2,false),(3,true),(30,false),(87,true),(0,false)]
theorem der_14879 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14879 :=
  CNF.rup_sound cl_14879 [cl_14877,cl_14878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14877 v h) (hints_cons _ _ _ (der_14878 v h) (by intro d hd; cases hd)))
def cl_14881 : CNF.NClause := [(4,false),(87,true),(30,false),(0,false),(3,true),(2,true)]
theorem der_14881 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14881 :=
  CNF.rup_sound cl_14881 [cl_1613,cl_1615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1613 v h) (hints_cons _ _ _ (inp_1615 v h) (by intro d hd; cases hd)))
def cl_14882 : CNF.NClause := [(4,true),(2,true),(30,false),(0,false),(87,true),(3,true)]
theorem der_14882 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14882 :=
  CNF.rup_sound cl_14882 [cl_1629,cl_1631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1629 v h) (hints_cons _ _ _ (inp_1631 v h) (by intro d hd; cases hd)))
def cl_14883 : CNF.NClause := [(87,true),(2,true),(30,false),(0,false),(3,true)]
theorem der_14883 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14883 :=
  CNF.rup_sound cl_14883 [cl_14881,cl_14882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14881 v h) (hints_cons _ _ _ (der_14882 v h) (by intro d hd; cases hd)))
def cl_14885 : CNF.NClause := [(35,false),(118,true),(61,false),(33,true),(34,true),(31,false)]
theorem der_14885 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14885 :=
  CNF.rup_sound cl_14885 [cl_3597,cl_3599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3597 v h) (hints_cons _ _ _ (inp_3599 v h) (by intro d hd; cases hd)))
def cl_14886 : CNF.NClause := [(118,true),(33,true),(61,false),(31,false),(34,true)]
theorem der_14886 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14886 :=
  CNF.rup_sound cl_14886 [cl_14841,cl_14885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14841 v h) (hints_cons _ _ _ (der_14885 v h) (by intro d hd; cases hd)))
def cl_14888 : CNF.NClause := [(35,false),(118,true),(61,false),(33,false),(34,true),(31,false)]
theorem der_14888 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14888 :=
  CNF.rup_sound cl_14888 [cl_3593,cl_3595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3593 v h) (hints_cons _ _ _ (inp_3595 v h) (by intro d hd; cases hd)))
def cl_14889 : CNF.NClause := [(35,true),(118,true),(61,false),(31,false),(33,false),(34,true)]
theorem der_14889 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14889 :=
  CNF.rup_sound cl_14889 [cl_3609,cl_3611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3609 v h) (hints_cons _ _ _ (inp_3611 v h) (by intro d hd; cases hd)))
def cl_14890 : CNF.NClause := [(118,true),(34,true),(61,false),(33,false),(31,false)]
theorem der_14890 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14890 :=
  CNF.rup_sound cl_14890 [cl_14888,cl_14889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14888 v h) (hints_cons _ _ _ (der_14889 v h) (by intro d hd; cases hd)))
def cl_14892 : CNF.NClause := [(35,true),(61,false),(118,true),(31,false),(33,false),(34,false)]
theorem der_14892 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14892 :=
  CNF.rup_sound cl_14892 [cl_3601,cl_3603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3601 v h) (hints_cons _ _ _ (inp_3603 v h) (by intro d hd; cases hd)))
def cl_14894 : CNF.NClause := [(35,false),(118,true),(61,false),(33,false),(34,false),(31,false)]
theorem der_14894 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14894 :=
  CNF.rup_sound cl_14894 [cl_3585,cl_3587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3585 v h) (hints_cons _ _ _ (inp_3587 v h) (by intro d hd; cases hd)))
def cl_14895 : CNF.NClause := [(118,true),(34,false),(61,false),(31,false),(33,false)]
theorem der_14895 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14895 :=
  CNF.rup_sound cl_14895 [cl_14892,cl_14894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14892 v h) (hints_cons _ _ _ (der_14894 v h) (by intro d hd; cases hd)))
def cl_14905 : CNF.NClause := [(112,true),(59,false),(40,false),(43,false),(46,false),(54,false)]
theorem der_14905 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14905 :=
  CNF.rup_sound cl_14905 [cl_3201,cl_3202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3201 v h) (hints_cons _ _ _ (inp_3202 v h) (by intro d hd; cases hd)))
def cl_14907 : CNF.NClause := [(86,true),(5,true),(29,false),(14,false),(18,false),(22,false)]
theorem der_14907 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14907 :=
  CNF.rup_sound cl_14907 [cl_1539,cl_1540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1539 v h) (hints_cons _ _ _ (inp_1540 v h) (by intro d hd; cases hd)))
def cl_14909 : CNF.NClause := [(35,true),(34,false),(61,false),(118,true),(33,true)]
theorem der_14909 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14909 :=
  CNF.rup_sound cl_14909 [cl_14831,cl_14837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14831 v h) (hints_cons _ _ _ (der_14837 v h) (by intro d hd; cases hd)))
def cl_14910 : CNF.NClause := [(33,true),(34,false),(118,true),(61,false)]
theorem der_14910 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14910 :=
  CNF.rup_sound cl_14910 [cl_14723,cl_14909] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14723 v h) (hints_cons _ _ _ (der_14909 v h) (by intro d hd; cases hd)))
def cl_14913 : CNF.NClause := [(99,true),(39,false),(51,false),(47,false),(60,false),(43,false)]
theorem der_14913 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14913 :=
  CNF.rup_sound cl_14913 [cl_2369,cl_2370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2369 v h) (hints_cons _ _ _ (inp_2370 v h) (by intro d hd; cases hd)))
def cl_14914 : CNF.NClause := [(95,true),(56,false),(38,false),(43,false),(48,false),(53,false)]
theorem der_14914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14914 :=
  CNF.rup_sound cl_14914 [cl_2113,cl_2114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2113 v h) (hints_cons _ _ _ (inp_2114 v h) (by intro d hd; cases hd)))
def cl_14916 : CNF.NClause := [(63,true),(9,false),(24,false),(25,false),(14,false),(19,false)]
theorem der_14916 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14916 :=
  CNF.rup_sound cl_14916 [cl_65,cl_66] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_65 v h) (hints_cons _ _ _ (inp_66 v h) (by intro d hd; cases hd)))
def cl_14917 : CNF.NClause := [(68,true),(8,false),(20,false),(29,false),(12,false),(16,false)]
theorem der_14917 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14917 :=
  CNF.rup_sound cl_14917 [cl_385,cl_386] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_385 v h) (hints_cons _ _ _ (inp_386 v h) (by intro d hd; cases hd)))
def cl_14918 : CNF.NClause := [(73,true),(7,false),(21,false),(28,false),(10,false),(18,false)]
theorem der_14918 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14918 :=
  CNF.rup_sound cl_14918 [cl_705,cl_706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_705 v h) (hints_cons _ _ _ (inp_706 v h) (by intro d hd; cases hd)))
def cl_14919 : CNF.NClause := [(78,true),(6,true),(27,false),(13,false),(15,false),(22,false)]
theorem der_14919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14919 :=
  CNF.rup_sound cl_14919 [cl_1027,cl_1028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1027 v h) (hints_cons _ _ _ (inp_1028 v h) (by intro d hd; cases hd)))
def cl_14920 : CNF.NClause := [(83,true),(5,true),(26,false),(11,false),(17,false),(23,false)]
theorem der_14920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14920 :=
  CNF.rup_sound cl_14920 [cl_1347,cl_1348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1347 v h) (hints_cons _ _ _ (inp_1348 v h) (by intro d hd; cases hd)))
def cl_14921 : CNF.NClause := [(64,true),(7,false),(22,false),(25,false),(12,false),(17,false)]
theorem der_14921 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14921 :=
  CNF.rup_sound cl_14921 [cl_129,cl_130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_129 v h) (hints_cons _ _ _ (inp_130 v h) (by intro d hd; cases hd)))
def cl_14922 : CNF.NClause := [(69,true),(9,false),(20,false),(27,false),(11,false),(18,false)]
theorem der_14922 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14922 :=
  CNF.rup_sound cl_14922 [cl_449,cl_450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_449 v h) (hints_cons _ _ _ (inp_450 v h) (by intro d hd; cases hd)))
def cl_14923 : CNF.NClause := [(74,true),(6,true),(29,false),(10,false),(19,false),(23,false)]
theorem der_14923 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14923 :=
  CNF.rup_sound cl_14923 [cl_771,cl_772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_771 v h) (hints_cons _ _ _ (inp_772 v h) (by intro d hd; cases hd)))
def cl_14924 : CNF.NClause := [(79,true),(8,false),(15,false),(26,false),(14,false),(21,false)]
theorem der_14924 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14924 :=
  CNF.rup_sound cl_14924 [cl_1089,cl_1090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1089 v h) (hints_cons _ _ _ (inp_1090 v h) (by intro d hd; cases hd)))
def cl_14925 : CNF.NClause := [(84,true),(5,true),(28,false),(13,false),(16,false),(24,false)]
theorem der_14925 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14925 :=
  CNF.rup_sound cl_14925 [cl_1411,cl_1412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1411 v h) (hints_cons _ _ _ (inp_1412 v h) (by intro d hd; cases hd)))
def cl_14926 : CNF.NClause := [(92,true),(5,true),(25,false),(10,false),(15,false),(20,false)]
theorem der_14926 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14926 :=
  CNF.rup_sound cl_14926 [cl_1923,cl_1924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1923 v h) (hints_cons _ _ _ (inp_1924 v h) (by intro d hd; cases hd)))
def cl_14940 : CNF.NClause := [(95,true),(56,false),(38,true),(43,false),(48,false),(53,false)]
theorem der_14940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14940 :=
  CNF.rup_sound cl_14940 [cl_2115,cl_2116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2115 v h) (hints_cons _ _ _ (inp_2116 v h) (by intro d hd; cases hd)))
def cl_14942 : CNF.NClause := [(64,true),(7,true),(25,false),(12,false),(17,false),(22,false)]
theorem der_14942 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14942 :=
  CNF.rup_sound cl_14942 [cl_131,cl_132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_131 v h) (hints_cons _ _ _ (inp_132 v h) (by intro d hd; cases hd)))
def cl_14945 : CNF.NClause := [(83,true),(5,false),(23,false),(26,false),(11,false),(17,false)]
theorem der_14945 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14945 :=
  CNF.rup_sound cl_14945 [cl_1345,cl_1346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1345 v h) (hints_cons _ _ _ (inp_1346 v h) (by intro d hd; cases hd)))
def cl_14947 : CNF.NClause := [(73,true),(7,true),(28,false),(10,false),(18,false),(21,false)]
theorem der_14947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14947 :=
  CNF.rup_sound cl_14947 [cl_707,cl_708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_707 v h) (hints_cons _ _ _ (inp_708 v h) (by intro d hd; cases hd)))
def cl_14949 : CNF.NClause := [(71,true),(7,true),(26,false),(13,false),(19,false),(20,false)]
theorem der_14949 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14949 :=
  CNF.rup_sound cl_14949 [cl_579,cl_580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_579 v h) (hints_cons _ _ _ (inp_580 v h) (by intro d hd; cases hd)))
def cl_14951 : CNF.NClause := [(78,true),(6,false),(22,false),(27,false),(13,false),(15,false)]
theorem der_14951 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14951 :=
  CNF.rup_sound cl_14951 [cl_1025,cl_1026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1025 v h) (hints_cons _ _ _ (inp_1026 v h) (by intro d hd; cases hd)))
def cl_14960 : CNF.NClause := [(87,true),(3,false),(1,false),(30,false),(2,false),(0,false)]
theorem der_14960 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14960 :=
  CNF.rup_sound cl_14960 [cl_1601,cl_14875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1601 v h) (hints_cons _ _ _ (der_14875 v h) (by intro d hd; cases hd)))
def cl_14978 : CNF.NClause := [(87,true),(3,true),(2,true),(30,false),(0,true),(1,false)]
theorem der_14978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14978 :=
  CNF.rup_sound cl_14978 [cl_1630,cl_14848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1630 v h) (hints_cons _ _ _ (der_14848 v h) (by intro d hd; cases hd)))
def cl_14980 : CNF.NClause := [(4,true),(87,true),(3,false),(30,false),(2,true)]
theorem der_14980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14980 :=
  CNF.rup_sound cl_14980 [cl_14836,cl_14833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14836 v h) (hints_cons _ _ _ (der_14833 v h) (by intro d hd; cases hd)))
def cl_14981 : CNF.NClause := [(87,true),(2,true),(30,false),(3,false)]
theorem der_14981 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14981 :=
  CNF.rup_sound cl_14981 [cl_14715,cl_14980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14715 v h) (hints_cons _ _ _ (der_14980 v h) (by intro d hd; cases hd)))
def cl_14991 : CNF.NClause := [(87,true),(3,true),(30,false),(2,false)]
theorem der_14991 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14991 :=
  CNF.rup_sound cl_14991 [cl_14879,cl_14873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14879 v h) (hints_cons _ _ _ (der_14873 v h) (by intro d hd; cases hd)))
def cl_14997 : CNF.NClause := [(87,true),(0,false),(30,false),(3,false),(2,false),(1,true)]
theorem der_14997 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_14997 :=
  CNF.rup_sound cl_14997 [cl_1603,cl_14875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1603 v h) (hints_cons _ _ _ (der_14875 v h) (by intro d hd; cases hd)))
def cl_15041 : CNF.NClause := [(89,true),(7,true),(27,false),(14,false),(16,false),(23,false)]
theorem der_15041 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15041 :=
  CNF.rup_sound cl_15041 [cl_1731,cl_1732] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1731 v h) (hints_cons _ _ _ (inp_1732 v h) (by intro d hd; cases hd)))
def cl_15075 : CNF.NClause := [(122,true),(57,false),(49,false),(43,false),(31,true),(55,false)]
theorem der_15075 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15075 :=
  CNF.rup_sound cl_15075 [cl_3842,cl_3844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3842 v h) (hints_cons _ _ _ (inp_3844 v h) (by intro d hd; cases hd)))
def cl_15077 : CNF.NClause := [(91,true),(12,false),(24,false),(26,false),(18,false)]
theorem der_15077 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15077 :=
  CNF.rup_sound cl_15077 [cl_14719,cl_14844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14719 v h) (hints_cons _ _ _ (der_14844 v h) (by intro d hd; cases hd)))
def cl_15079 : CNF.NClause := [(78,true),(13,false),(22,false),(27,false),(15,false)]
theorem der_15079 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15079 :=
  CNF.rup_sound cl_15079 [cl_14951,cl_14919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14951 v h) (hints_cons _ _ _ (der_14919 v h) (by intro d hd; cases hd)))
def cl_15081 : CNF.NClause := [(66,true),(11,false),(21,false),(25,false),(16,false)]
theorem der_15081 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15081 :=
  CNF.rup_sound cl_15081 [cl_14704,cl_14814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14704 v h) (hints_cons _ _ _ (der_14814 v h) (by intro d hd; cases hd)))
def cl_15083 : CNF.NClause := [(70,true),(3,true),(28,false),(14,false),(17,false),(20,false)]
theorem der_15083 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15083 :=
  CNF.rup_sound cl_15083 [cl_514,cl_516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_514 v h) (hints_cons _ _ _ (inp_516 v h) (by intro d hd; cases hd)))
def cl_15085 : CNF.NClause := [(74,true),(2,false),(29,false),(23,false),(10,false),(19,false)]
theorem der_15085 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15085 :=
  CNF.rup_sound cl_15085 [cl_769,cl_14923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_769 v h) (hints_cons _ _ _ (der_14923 v h) (by intro d hd; cases hd)))
def cl_15087 : CNF.NClause := [(82,true),(5,true),(30,false),(7,true),(8,false),(9,false)]
theorem der_15087 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15087 :=
  CNF.rup_sound cl_15087 [cl_1286,cl_1288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1286 v h) (hints_cons _ _ _ (inp_1288 v h) (by intro d hd; cases hd)))
def cl_15089 : CNF.NClause := [(74,true),(2,true),(29,false),(10,false),(19,false),(23,false)]
theorem der_15089 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15089 :=
  CNF.rup_sound cl_15089 [cl_770,cl_14923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_770 v h) (hints_cons _ _ _ (der_14923 v h) (by intro d hd; cases hd)))
def cl_15094 : CNF.NClause := [(105,true),(33,false),(60,false),(50,false),(41,false),(54,false)]
theorem der_15094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15094 :=
  CNF.rup_sound cl_15094 [cl_2753,cl_2755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2753 v h) (hints_cons _ _ _ (inp_2755 v h) (by intro d hd; cases hd)))
def cl_15097 : CNF.NClause := [(87,true),(0,false),(30,false),(3,false),(2,false)]
theorem der_15097 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15097 :=
  CNF.rup_sound cl_15097 [cl_14997,cl_14960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14997 v h) (hints_cons _ _ _ (der_14960 v h) (by intro d hd; cases hd)))
def cl_15098 : CNF.NClause := [(87,true),(3,false),(2,false),(30,false)]
theorem der_15098 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15098 :=
  CNF.rup_sound cl_15098 [cl_14873,cl_15097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14873 v h) (hints_cons _ _ _ (der_15097 v h) (by intro d hd; cases hd)))
def cl_15100 : CNF.NClause := [(70,true),(3,false),(20,false),(28,false),(14,false),(17,false)]
theorem der_15100 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15100 :=
  CNF.rup_sound cl_15100 [cl_513,cl_515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_513 v h) (hints_cons _ _ _ (inp_515 v h) (by intro d hd; cases hd)))
def cl_15102 : CNF.NClause := [(76,true),(8,true),(27,false),(10,false),(17,false),(24,false)]
theorem der_15102 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15102 :=
  CNF.rup_sound cl_15102 [cl_899,cl_900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_899 v h) (hints_cons _ _ _ (inp_900 v h) (by intro d hd; cases hd)))
def cl_15104 : CNF.NClause := [(82,true),(5,false),(7,false),(30,false),(8,true),(9,false)]
theorem der_15104 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15104 :=
  CNF.rup_sound cl_15104 [cl_1289,cl_1291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1289 v h) (hints_cons _ _ _ (inp_1291 v h) (by intro d hd; cases hd)))
def cl_15106 : CNF.NClause := [(82,true),(5,true),(30,false),(7,false),(8,true),(9,false)]
theorem der_15106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15106 :=
  CNF.rup_sound cl_15106 [cl_1290,cl_1292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1290 v h) (hints_cons _ _ _ (inp_1292 v h) (by intro d hd; cases hd)))
def cl_15108 : CNF.NClause := [(83,true),(11,false),(23,false),(26,false),(17,false)]
theorem der_15108 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15108 :=
  CNF.rup_sound cl_15108 [cl_14945,cl_14920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14945 v h) (hints_cons _ _ _ (der_14920 v h) (by intro d hd; cases hd)))
def cl_15110 : CNF.NClause := [(86,true),(14,false),(22,false),(29,false),(18,false)]
theorem der_15110 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15110 :=
  CNF.rup_sound cl_15110 [cl_14712,cl_14907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14712 v h) (hints_cons _ _ _ (der_14907 v h) (by intro d hd; cases hd)))
def cl_15113 : CNF.NClause := [(68,true),(8,true),(29,false),(12,false),(16,false),(20,false)]
theorem der_15113 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15113 :=
  CNF.rup_sound cl_15113 [cl_387,cl_388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_387 v h) (hints_cons _ _ _ (inp_388 v h) (by intro d hd; cases hd)))
def cl_15119 : CNF.NClause := [(90,true),(8,true),(28,false),(11,false),(19,false),(22,false)]
theorem der_15119 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15119 :=
  CNF.rup_sound cl_15119 [cl_1795,cl_1796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1795 v h) (hints_cons _ _ _ (inp_1796 v h) (by intro d hd; cases hd)))
def cl_15124 : CNF.NClause := [(101,true),(59,false),(48,false),(34,false),(45,false),(51,false)]
theorem der_15124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15124 :=
  CNF.rup_sound cl_15124 [cl_2497,cl_2499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2497 v h) (hints_cons _ _ _ (inp_2499 v h) (by intro d hd; cases hd)))
def cl_15128 : CNF.NClause := [(82,true),(5,true),(30,false),(7,true),(8,true),(9,false)]
theorem der_15128 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15128 :=
  CNF.rup_sound cl_15128 [cl_1294,cl_1296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1294 v h) (hints_cons _ _ _ (inp_1296 v h) (by intro d hd; cases hd)))
def cl_15131 : CNF.NClause := [(82,true),(7,true),(5,false),(30,false),(8,true),(9,false)]
theorem der_15131 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15131 :=
  CNF.rup_sound cl_15131 [cl_1293,cl_1295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1293 v h) (hints_cons _ _ _ (inp_1295 v h) (by intro d hd; cases hd)))
def cl_15133 : CNF.NClause := [(118,true),(61,false),(31,false),(34,false)]
theorem der_15133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15133 :=
  CNF.rup_sound cl_15133 [cl_14895,cl_14910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14895 v h) (hints_cons _ _ _ (der_14910 v h) (by intro d hd; cases hd)))
def cl_15135 : CNF.NClause := [(87,true),(75,false),(34,false),(70,false),(65,false),(80,false),(85,false)]
theorem der_15135 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15135 :=
  CNF.rup_sound cl_15135 [cl_4418,cl_4417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4418 v h) (hints_cons _ _ _ (inp_4417 v h) (by intro d hd; cases hd)))
def cl_15136 : CNF.NClause := [(96,true),(56,false),(34,false),(44,false),(49,false),(39,true)]
theorem der_15136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15136 :=
  CNF.rup_sound cl_15136 [cl_2179,cl_2195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2179 v h) (hints_cons _ _ _ (inp_2195 v h) (by intro d hd; cases hd)))
def cl_15137 : CNF.NClause := [(116,true),(36,false),(58,false),(52,false),(43,false),(34,false)]
theorem der_15137 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15137 :=
  CNF.rup_sound cl_15137 [cl_3457,cl_3465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3457 v h) (hints_cons _ _ _ (inp_3465 v h) (by intro d hd; cases hd)))
def cl_15138 : CNF.NClause := [(74,true),(10,false),(29,false),(23,false),(19,false)]
theorem der_15138 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15138 :=
  CNF.rup_sound cl_15138 [cl_15085,cl_15089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15085 v h) (hints_cons _ _ _ (der_15089 v h) (by intro d hd; cases hd)))
def cl_15140 : CNF.NClause := [(75,true),(9,false),(22,false),(26,false),(10,false),(16,false)]
theorem der_15140 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15140 :=
  CNF.rup_sound cl_15140 [cl_833,cl_834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_833 v h) (hints_cons _ _ _ (inp_834 v h) (by intro d hd; cases hd)))
def cl_15141 : CNF.NClause := [(3,true),(80,false),(70,false),(34,false),(75,false),(65,false),(85,false)]
theorem der_15141 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15141 :=
  CNF.rup_sound cl_15141 [cl_4354,cl_15135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4354 v h) (hints_cons _ _ _ (der_15135 v h) (by intro d hd; cases hd)))
def cl_15144 : CNF.NClause := [(65,true),(8,true),(25,false),(13,false),(18,false),(23,false)]
theorem der_15144 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15144 :=
  CNF.rup_sound cl_15144 [cl_195,cl_196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_195 v h) (hints_cons _ _ _ (inp_196 v h) (by intro d hd; cases hd)))
def cl_15147 : CNF.NClause := [(87,true),(3,false),(30,false)]
theorem der_15147 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15147 :=
  CNF.rup_sound cl_15147 [cl_14981,cl_15098] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14981 v h) (hints_cons _ _ _ (der_15098 v h) (by intro d hd; cases hd)))
def cl_15149 : CNF.NClause := [(87,true),(3,true),(0,false),(30,false)]
theorem der_15149 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15149 :=
  CNF.rup_sound cl_15149 [cl_14991,cl_14883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14991 v h) (hints_cons _ _ _ (der_14883 v h) (by intro d hd; cases hd)))
def cl_15150 : CNF.NClause := [(118,true),(34,true),(61,false),(31,false)]
theorem der_15150 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15150 :=
  CNF.rup_sound cl_15150 [cl_14890,cl_14886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14890 v h) (hints_cons _ _ _ (der_14886 v h) (by intro d hd; cases hd)))
def cl_15152 : CNF.NClause := [(84,true),(5,false),(24,false),(28,false),(13,false),(16,false)]
theorem der_15152 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15152 :=
  CNF.rup_sound cl_15152 [cl_1409,cl_1410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1409 v h) (hints_cons _ _ _ (inp_1410 v h) (by intro d hd; cases hd)))
def cl_15154 : CNF.NClause := [(79,true),(8,true),(26,false),(14,false),(15,false),(21,false)]
theorem der_15154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15154 :=
  CNF.rup_sound cl_15154 [cl_1091,cl_1092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1091 v h) (hints_cons _ _ _ (inp_1092 v h) (by intro d hd; cases hd)))
def cl_15155 : CNF.NClause := [(70,true),(14,false),(20,false),(28,false),(17,false)]
theorem der_15155 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15155 :=
  CNF.rup_sound cl_15155 [cl_15100,cl_15083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15100 v h) (hints_cons _ _ _ (der_15083 v h) (by intro d hd; cases hd)))
def cl_15162 : CNF.NClause := [(99,true),(60,false),(39,true),(43,false),(47,false),(51,false)]
theorem der_15162 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15162 :=
  CNF.rup_sound cl_15162 [cl_2371,cl_2372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2371 v h) (hints_cons _ _ _ (inp_2372 v h) (by intro d hd; cases hd)))
def cl_15163 : CNF.NClause := [(103,true),(45,false),(42,false),(44,false),(43,false),(41,false)]
theorem der_15163 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15163 :=
  CNF.rup_sound cl_15163 [cl_2625,cl_2657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2625 v h) (hints_cons _ _ _ (inp_2657 v h) (by intro d hd; cases hd)))
def cl_15165 : CNF.NClause := [(122,true),(31,false),(55,false),(43,false),(57,false),(49,false)]
theorem der_15165 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15165 :=
  CNF.rup_sound cl_15165 [cl_3843,cl_3841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3843 v h) (hints_cons _ _ _ (inp_3841 v h) (by intro d hd; cases hd)))
def cl_15166 : CNF.NClause := [(122,true),(49,false),(55,false),(43,false),(57,false)]
theorem der_15166 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15166 :=
  CNF.rup_sound cl_15166 [cl_15075,cl_15165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15075 v h) (hints_cons _ _ _ (der_15165 v h) (by intro d hd; cases hd)))
def cl_15167 : CNF.NClause := [(95,true),(56,false),(48,false),(43,false),(53,false)]
theorem der_15167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15167 :=
  CNF.rup_sound cl_15167 [cl_14914,cl_14940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14914 v h) (hints_cons _ _ _ (der_14940 v h) (by intro d hd; cases hd)))
def cl_15170 : CNF.NClause := [(112,true),(40,true),(59,false),(43,false),(46,false),(54,false)]
theorem der_15170 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15170 :=
  CNF.rup_sound cl_15170 [cl_3203,cl_3204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3203 v h) (hints_cons _ _ _ (inp_3204 v h) (by intro d hd; cases hd)))
def cl_15171 : CNF.NClause := [(34,false),(116,true),(52,false),(58,false),(50,false),(43,false)]
theorem der_15171 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15171 :=
  CNF.rup_sound cl_15171 [cl_15137,cl_3459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15137 v h) (hints_cons _ _ _ (inp_3459 v h) (by intro d hd; cases hd)))
def cl_15172 : CNF.NClause := [(34,true),(116,true),(52,false),(43,false),(50,false),(58,false)]
theorem der_15172 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15172 :=
  CNF.rup_sound cl_15172 [cl_3458,cl_3460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3458 v h) (hints_cons _ _ _ (inp_3460 v h) (by intro d hd; cases hd)))
def cl_15173 : CNF.NClause := [(116,true),(52,false),(43,false),(58,false),(50,false)]
theorem der_15173 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15173 :=
  CNF.rup_sound cl_15173 [cl_15171,cl_15172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15171 v h) (hints_cons _ _ _ (der_15172 v h) (by intro d hd; cases hd)))
def cl_15175 : CNF.NClause := [(64,true),(12,false),(22,false),(25,false),(17,false)]
theorem der_15175 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15175 :=
  CNF.rup_sound cl_15175 [cl_14921,cl_14942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14921 v h) (hints_cons _ _ _ (der_14942 v h) (by intro d hd; cases hd)))
def cl_15177 : CNF.NClause := [(73,true),(10,false),(21,false),(28,false),(18,false)]
theorem der_15177 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15177 :=
  CNF.rup_sound cl_15177 [cl_14918,cl_14947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14918 v h) (hints_cons _ _ _ (der_14947 v h) (by intro d hd; cases hd)))
def cl_15179 : CNF.NClause := [(71,true),(13,false),(20,false),(26,false),(19,false)]
theorem der_15179 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15179 :=
  CNF.rup_sound cl_15179 [cl_14706,cl_14949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14706 v h) (hints_cons _ _ _ (der_14949 v h) (by intro d hd; cases hd)))
def cl_15180 : CNF.NClause := [(92,true),(10,false),(20,false),(25,false),(15,false)]
theorem der_15180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15180 :=
  CNF.rup_sound cl_15180 [cl_14720,cl_14926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14720 v h) (hints_cons _ _ _ (der_14926 v h) (by intro d hd; cases hd)))
def cl_15182 : CNF.NClause := [(80,true),(7,true),(29,false),(11,false),(15,false),(24,false)]
theorem der_15182 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15182 :=
  CNF.rup_sound cl_15182 [cl_1155,cl_1156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1155 v h) (hints_cons _ _ _ (inp_1156 v h) (by intro d hd; cases hd)))
def cl_15183 : CNF.NClause := [(80,true),(7,false),(24,false),(11,false),(29,false),(15,false)]
theorem der_15183 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15183 :=
  CNF.rup_sound cl_15183 [cl_1153,cl_1154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1153 v h) (hints_cons _ _ _ (inp_1154 v h) (by intro d hd; cases hd)))
def cl_15184 : CNF.NClause := [(80,true),(11,false),(29,false),(24,false),(15,false)]
theorem der_15184 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15184 :=
  CNF.rup_sound cl_15184 [cl_15182,cl_15183] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15182 v h) (hints_cons _ _ _ (der_15183 v h) (by intro d hd; cases hd)))
def cl_15185 : CNF.NClause := [(84,true),(13,false),(24,false),(28,false),(16,false)]
theorem der_15185 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15185 :=
  CNF.rup_sound cl_15185 [cl_15152,cl_14925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15152 v h) (hints_cons _ _ _ (der_14925 v h) (by intro d hd; cases hd)))
def cl_15187 : CNF.NClause := [(89,true),(14,false),(23,false),(27,false),(16,false)]
theorem der_15187 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15187 :=
  CNF.rup_sound cl_15187 [cl_14717,cl_15041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14717 v h) (hints_cons _ _ _ (der_15041 v h) (by intro d hd; cases hd)))
def cl_15188 : CNF.NClause := [(5,true),(85,true),(27,false),(12,false),(19,false),(21,false)]
theorem der_15188 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15188 :=
  CNF.rup_sound cl_15188 [cl_1475,cl_1476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1475 v h) (hints_cons _ _ _ (inp_1476 v h) (by intro d hd; cases hd)))
def cl_15189 : CNF.NClause := [(5,false),(85,true),(27,false),(21,false),(12,false),(19,false)]
theorem der_15189 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15189 :=
  CNF.rup_sound cl_15189 [cl_1473,cl_1474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1473 v h) (hints_cons _ _ _ (inp_1474 v h) (by intro d hd; cases hd)))
def cl_15190 : CNF.NClause := [(85,true),(12,false),(27,false),(21,false),(19,false)]
theorem der_15190 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15190 :=
  CNF.rup_sound cl_15190 [cl_15188,cl_15189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15188 v h) (hints_cons _ _ _ (der_15189 v h) (by intro d hd; cases hd)))
def cl_15191 : CNF.NClause := [(68,true),(12,false),(20,false),(29,false),(16,false)]
theorem der_15191 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15191 :=
  CNF.rup_sound cl_15191 [cl_14917,cl_15113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14917 v h) (hints_cons _ _ _ (der_15113 v h) (by intro d hd; cases hd)))
def cl_15192 : CNF.NClause := [(81,true),(9,true),(28,false),(12,false),(15,false),(23,false)]
theorem der_15192 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15192 :=
  CNF.rup_sound cl_15192 [cl_1219,cl_1220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1219 v h) (hints_cons _ _ _ (inp_1220 v h) (by intro d hd; cases hd)))
def cl_15193 : CNF.NClause := [(81,true),(12,false),(23,false),(28,false),(15,false)]
theorem der_15193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15193 :=
  CNF.rup_sound cl_15193 [cl_14710,cl_15192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14710 v h) (hints_cons _ _ _ (der_15192 v h) (by intro d hd; cases hd)))
def cl_15194 : CNF.NClause := [(9,true),(3,true),(413,true),(419,true),(425,true),(429,true)]
theorem der_15194 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15194 :=
  CNF.rup_sound cl_15194 [cl_13744,cl_14039,cl_9724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13744 v h) (hints_cons _ _ _ (inp_14039 v h) (hints_cons _ _ _ (inp_9724 v h) (by intro d hd; cases hd))))
def cl_15205 : CNF.NClause := [(69,true),(9,true),(27,false),(11,false),(18,false),(20,false)]
theorem der_15205 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15205 :=
  CNF.rup_sound cl_15205 [cl_451,cl_452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_451 v h) (hints_cons _ _ _ (inp_452 v h) (by intro d hd; cases hd)))
def cl_15209 : CNF.NClause := [(88,true),(9,true),(29,false),(13,false),(17,false),(21,false)]
theorem der_15209 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15209 :=
  CNF.rup_sound cl_15209 [cl_1667,cl_1668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1667 v h) (hints_cons _ _ _ (inp_1668 v h) (by intro d hd; cases hd)))
def cl_15213 : CNF.NClause := [(63,true),(9,true),(25,false),(14,false),(19,false),(24,false)]
theorem der_15213 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15213 :=
  CNF.rup_sound cl_15213 [cl_67,cl_68] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_67 v h) (hints_cons _ _ _ (inp_68 v h) (by intro d hd; cases hd)))
def cl_15220 : CNF.NClause := [(82,true),(7,false),(30,false),(6,false),(8,true),(9,true)]
theorem der_15220 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15220 :=
  CNF.rup_sound cl_15220 [cl_1305,cl_1306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1305 v h) (hints_cons _ _ _ (inp_1306 v h) (by intro d hd; cases hd)))
def cl_15222 : CNF.NClause := [(82,true),(6,false),(30,false),(7,true),(8,true),(9,true)]
theorem der_15222 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15222 :=
  CNF.rup_sound cl_15222 [cl_1310,cl_1309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1310 v h) (hints_cons _ _ _ (inp_1309 v h) (by intro d hd; cases hd)))
def cl_15223 : CNF.NClause := [(82,true),(6,false),(30,false),(9,true),(8,true)]
theorem der_15223 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15223 :=
  CNF.rup_sound cl_15223 [cl_15220,cl_15222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15220 v h) (hints_cons _ _ _ (der_15222 v h) (by intro d hd; cases hd)))
def cl_15234 : CNF.NClause := [(82,true),(8,false),(9,false),(5,false),(7,false),(30,false)]
theorem der_15234 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15234 :=
  CNF.rup_sound cl_15234 [cl_1281,cl_1283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1281 v h) (hints_cons _ _ _ (inp_1283 v h) (by intro d hd; cases hd)))
def cl_15235 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false)]
theorem der_15235 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15235 :=
  CNF.rup_sound cl_15235 [cl_2626,cl_2658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2626 v h) (hints_cons _ _ _ (inp_2658 v h) (by intro d hd; cases hd)))
def cl_15237 : CNF.NClause := [(99,true),(60,true),(51,false),(43,false),(39,false),(47,false)]
theorem der_15237 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15237 :=
  CNF.rup_sound cl_15237 [cl_2401,cl_2402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2401 v h) (hints_cons _ _ _ (inp_2402 v h) (by intro d hd; cases hd)))
def cl_15238 : CNF.NClause := [(112,true),(40,false),(59,false),(43,false),(46,false),(54,true)]
theorem der_15238 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15238 :=
  CNF.rup_sound cl_15238 [cl_3217,cl_3218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3217 v h) (hints_cons _ _ _ (inp_3218 v h) (by intro d hd; cases hd)))
def cl_15239 : CNF.NClause := [(116,true),(50,true),(58,false),(36,false),(43,false),(52,false)]
theorem der_15239 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15239 :=
  CNF.rup_sound cl_15239 [cl_3466,cl_15137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3466 v h) (hints_cons _ _ _ (der_15137 v h) (by intro d hd; cases hd)))
def cl_15241 : CNF.NClause := [(75,true),(9,false),(26,false),(10,true),(16,false),(22,false)]
theorem der_15241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15241 :=
  CNF.rup_sound cl_15241 [cl_837,cl_838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_837 v h) (hints_cons _ _ _ (inp_838 v h) (by intro d hd; cases hd)))
def cl_15243 : CNF.NClause := [(65,true),(8,false),(23,false),(25,false),(13,false),(18,false)]
theorem der_15243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15243 :=
  CNF.rup_sound cl_15243 [cl_193,cl_194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_193 v h) (hints_cons _ _ _ (inp_194 v h) (by intro d hd; cases hd)))
def cl_15246 : CNF.NClause := [(74,true),(6,false),(29,false),(10,true),(19,false),(23,false)]
theorem der_15246 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15246 :=
  CNF.rup_sound cl_15246 [cl_773,cl_774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_773 v h) (hints_cons _ _ _ (inp_774 v h) (by intro d hd; cases hd)))
def cl_15249 : CNF.NClause := [(76,true),(8,false),(27,false),(10,true),(17,false),(24,false)]
theorem der_15249 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15249 :=
  CNF.rup_sound cl_15249 [cl_901,cl_902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_901 v h) (hints_cons _ _ _ (inp_902 v h) (by intro d hd; cases hd)))
def cl_15251 : CNF.NClause := [(92,true),(0,false),(25,false),(10,true),(15,false),(20,false)]
theorem der_15251 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15251 :=
  CNF.rup_sound cl_15251 [cl_1925,cl_1927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1925 v h) (hints_cons _ _ _ (inp_1927 v h) (by intro d hd; cases hd)))
def cl_15254 : CNF.NClause := [(82,true),(8,false),(5,false),(7,true),(30,false),(9,false)]
theorem der_15254 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15254 :=
  CNF.rup_sound cl_15254 [cl_1285,cl_1287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1285 v h) (hints_cons _ _ _ (inp_1287 v h) (by intro d hd; cases hd)))
def cl_15264 : CNF.NClause := [(73,true),(7,false),(28,false),(10,true),(18,false),(21,false)]
theorem der_15264 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15264 :=
  CNF.rup_sound cl_15264 [cl_709,cl_710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_709 v h) (hints_cons _ _ _ (inp_710 v h) (by intro d hd; cases hd)))
def cl_15268 : CNF.NClause := [(6,true),(74,true),(29,false),(10,true),(19,false),(23,false)]
theorem der_15268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15268 :=
  CNF.rup_sound cl_15268 [cl_775,cl_776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_775 v h) (hints_cons _ _ _ (inp_776 v h) (by intro d hd; cases hd)))
def cl_15269 : CNF.NClause := [(74,true),(10,true),(29,false),(23,false),(19,false)]
theorem der_15269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15269 :=
  CNF.rup_sound cl_15269 [cl_15246,cl_15268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15246 v h) (hints_cons _ _ _ (der_15268 v h) (by intro d hd; cases hd)))
def cl_15272 : CNF.NClause := [(0,true),(92,true),(10,true),(25,false),(15,false),(20,false)]
theorem der_15272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15272 :=
  CNF.rup_sound cl_15272 [cl_1928,cl_1926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1928 v h) (hints_cons _ _ _ (inp_1926 v h) (by intro d hd; cases hd)))
def cl_15273 : CNF.NClause := [(92,true),(10,true),(25,false),(20,false),(15,false)]
theorem der_15273 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15273 :=
  CNF.rup_sound cl_15273 [cl_15251,cl_15272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15251 v h) (hints_cons _ _ _ (der_15272 v h) (by intro d hd; cases hd)))
def cl_15280 : CNF.NClause := [(75,true),(9,true),(26,false),(10,true),(16,false),(22,false)]
theorem der_15280 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15280 :=
  CNF.rup_sound cl_15280 [cl_839,cl_840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_839 v h) (hints_cons _ _ _ (inp_840 v h) (by intro d hd; cases hd)))
def cl_15284 : CNF.NClause := [(65,true),(13,false),(23,false),(25,false),(18,false)]
theorem der_15284 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15284 :=
  CNF.rup_sound cl_15284 [cl_15243,cl_15144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15243 v h) (hints_cons _ _ _ (der_15144 v h) (by intro d hd; cases hd)))
def cl_15286 : CNF.NClause := [(73,true),(4,false),(10,true),(18,false),(21,false),(28,false)]
theorem der_15286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15286 :=
  CNF.rup_sound cl_15286 [cl_15264,cl_711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15264 v h) (hints_cons _ _ _ (inp_711 v h) (by intro d hd; cases hd)))
def cl_15288 : CNF.NClause := [(90,true),(11,false),(22,false),(28,false),(19,false)]
theorem der_15288 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15288 :=
  CNF.rup_sound cl_15288 [cl_14718,cl_15119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14718 v h) (hints_cons _ _ _ (der_15119 v h) (by intro d hd; cases hd)))
def cl_15290 : CNF.NClause := [(79,true),(14,false),(15,false),(26,false),(21,false)]
theorem der_15290 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15290 :=
  CNF.rup_sound cl_15290 [cl_14924,cl_15154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14924 v h) (hints_cons _ _ _ (der_15154 v h) (by intro d hd; cases hd)))
def cl_15292 : CNF.NClause := [(76,true),(8,true),(27,false),(10,true),(17,false),(24,false)]
theorem der_15292 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15292 :=
  CNF.rup_sound cl_15292 [cl_903,cl_904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_903 v h) (hints_cons _ _ _ (inp_904 v h) (by intro d hd; cases hd)))
def cl_15293 : CNF.NClause := [(76,true),(10,true),(27,false),(24,false),(17,false)]
theorem der_15293 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15293 :=
  CNF.rup_sound cl_15293 [cl_15249,cl_15292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15249 v h) (hints_cons _ _ _ (der_15292 v h) (by intro d hd; cases hd)))
def cl_15295 : CNF.NClause := [(73,true),(7,true),(10,true),(28,false),(18,false),(21,false)]
theorem der_15295 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15295 :=
  CNF.rup_sound cl_15295 [cl_712,cl_15286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_712 v h) (hints_cons _ _ _ (der_15286 v h) (by intro d hd; cases hd)))
def cl_15296 : CNF.NClause := [(73,true),(10,true),(28,false),(21,false),(18,false)]
theorem der_15296 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15296 :=
  CNF.rup_sound cl_15296 [cl_15264,cl_15295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15264 v h) (hints_cons _ _ _ (der_15295 v h) (by intro d hd; cases hd)))
def cl_15298 : CNF.NClause := [(82,true),(8,true),(9,false),(30,false),(7,true)]
theorem der_15298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15298 :=
  CNF.rup_sound cl_15298 [cl_15131,cl_15128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15131 v h) (hints_cons _ _ _ (der_15128 v h) (by intro d hd; cases hd)))
def cl_15302 : CNF.NClause := [(82,true),(5,true),(30,false),(7,false),(8,false),(9,false)]
theorem der_15302 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15302 :=
  CNF.rup_sound cl_15302 [cl_1284,cl_1282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1284 v h) (hints_cons _ _ _ (inp_1282 v h) (by intro d hd; cases hd)))
def cl_15304 : CNF.NClause := [(82,true),(9,false),(30,false),(7,false),(8,true)]
theorem der_15304 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15304 :=
  CNF.rup_sound cl_15304 [cl_15106,cl_15104] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15106 v h) (hints_cons _ _ _ (der_15104 v h) (by intro d hd; cases hd)))
def cl_15308 : CNF.NClause := [(82,true),(9,false),(8,false),(7,true),(30,false)]
theorem der_15308 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15308 :=
  CNF.rup_sound cl_15308 [cl_15254,cl_15087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15254 v h) (hints_cons _ _ _ (der_15087 v h) (by intro d hd; cases hd)))
def cl_15310 : CNF.NClause := [(7,false),(82,true),(8,false),(9,false),(30,false)]
theorem der_15310 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15310 :=
  CNF.rup_sound cl_15310 [cl_15234,cl_15302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15234 v h) (hints_cons _ _ _ (der_15302 v h) (by intro d hd; cases hd)))
def cl_15311 : CNF.NClause := [(82,true),(8,false),(9,false),(30,false)]
theorem der_15311 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15311 :=
  CNF.rup_sound cl_15311 [cl_15308,cl_15310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15308 v h) (hints_cons _ _ _ (der_15310 v h) (by intro d hd; cases hd)))
def cl_15321 : CNF.NClause := [(66,true),(6,false),(25,false),(11,true),(16,false),(21,false)]
theorem der_15321 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15321 :=
  CNF.rup_sound cl_15321 [cl_261,cl_262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_261 v h) (hints_cons _ _ _ (inp_262 v h) (by intro d hd; cases hd)))
def cl_15323 : CNF.NClause := [(83,true),(4,false),(26,false),(11,true),(17,false),(23,false)]
theorem der_15323 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15323 :=
  CNF.rup_sound cl_15323 [cl_1349,cl_1351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1349 v h) (hints_cons _ _ _ (inp_1351 v h) (by intro d hd; cases hd)))
def cl_15325 : CNF.NClause := [(83,true),(5,false),(11,true),(17,false),(23,false),(26,false)]
theorem der_15325 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15325 :=
  CNF.rup_sound cl_15325 [cl_15323,cl_1350] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15323 v h) (hints_cons _ _ _ (inp_1350 v h) (by intro d hd; cases hd)))
def cl_15328 : CNF.NClause := [(90,true),(8,false),(28,false),(11,true),(19,false),(22,false)]
theorem der_15328 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15328 :=
  CNF.rup_sound cl_15328 [cl_1797,cl_1798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1797 v h) (hints_cons _ _ _ (inp_1798 v h) (by intro d hd; cases hd)))
def cl_15338 : CNF.NClause := [(66,true),(1,false),(11,true),(16,false),(21,false),(25,false)]
theorem der_15338 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15338 :=
  CNF.rup_sound cl_15338 [cl_15321,cl_263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15321 v h) (hints_cons _ _ _ (inp_263 v h) (by intro d hd; cases hd)))
def cl_15362 : CNF.NClause := [(80,true),(3,false),(29,false),(11,true),(15,false),(24,false)]
theorem der_15362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15362 :=
  CNF.rup_sound cl_15362 [cl_1157,cl_1159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1157 v h) (hints_cons _ _ _ (inp_1159 v h) (by intro d hd; cases hd)))
def cl_15363 : CNF.NClause := [(103,true),(42,true),(41,false),(43,false),(44,false),(45,false)]
theorem der_15363 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15363 :=
  CNF.rup_sound cl_15363 [cl_2627,cl_2659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2627 v h) (hints_cons _ _ _ (inp_2659 v h) (by intro d hd; cases hd)))
def cl_15365 : CNF.NClause := [(3,true),(80,true),(29,false),(11,true),(15,false),(24,false)]
theorem der_15365 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15365 :=
  CNF.rup_sound cl_15365 [cl_1158,cl_1160] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1158 v h) (hints_cons _ _ _ (inp_1160 v h) (by intro d hd; cases hd)))
def cl_15366 : CNF.NClause := [(80,true),(11,true),(29,false),(24,false),(15,false)]
theorem der_15366 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15366 :=
  CNF.rup_sound cl_15366 [cl_15362,cl_15365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15362 v h) (hints_cons _ _ _ (der_15365 v h) (by intro d hd; cases hd)))
def cl_15369 : CNF.NClause := [(9,false),(69,true),(27,false),(11,true),(18,false),(20,false)]
theorem der_15369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15369 :=
  CNF.rup_sound cl_15369 [cl_453,cl_454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_453 v h) (hints_cons _ _ _ (inp_454 v h) (by intro d hd; cases hd)))
def cl_15370 : CNF.NClause := [(9,true),(69,true),(27,false),(11,true),(18,false),(20,false)]
theorem der_15370 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15370 :=
  CNF.rup_sound cl_15370 [cl_455,cl_456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_455 v h) (hints_cons _ _ _ (inp_456 v h) (by intro d hd; cases hd)))
def cl_15371 : CNF.NClause := [(69,true),(11,true),(27,false),(20,false),(18,false)]
theorem der_15371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15371 :=
  CNF.rup_sound cl_15371 [cl_15369,cl_15370] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15369 v h) (hints_cons _ _ _ (der_15370 v h) (by intro d hd; cases hd)))
def cl_15373 : CNF.NClause := [(66,true),(6,true),(11,true),(25,false),(16,false),(21,false)]
theorem der_15373 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15373 :=
  CNF.rup_sound cl_15373 [cl_264,cl_15338] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_264 v h) (hints_cons _ _ _ (der_15338 v h) (by intro d hd; cases hd)))
def cl_15374 : CNF.NClause := [(66,true),(11,true),(25,false),(21,false),(16,false)]
theorem der_15374 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15374 :=
  CNF.rup_sound cl_15374 [cl_15321,cl_15373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15321 v h) (hints_cons _ _ _ (der_15373 v h) (by intro d hd; cases hd)))
def cl_15377 : CNF.NClause := [(76,true),(10,false),(24,false),(27,false),(17,false)]
theorem der_15377 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15377 :=
  CNF.rup_sound cl_15377 [cl_14708,cl_15102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14708 v h) (hints_cons _ _ _ (der_15102 v h) (by intro d hd; cases hd)))
def cl_15384 : CNF.NClause := [(83,true),(11,true),(26,false),(23,false),(17,false)]
theorem der_15384 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15384 :=
  CNF.rup_sound cl_15384 [cl_15323,cl_15325,cl_1352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15323 v h) (hints_cons _ _ _ (der_15325 v h) (hints_cons _ _ _ (inp_1352 v h) (by intro d hd; cases hd))))
def cl_15392 : CNF.NClause := [(75,true),(9,true),(26,false),(10,false),(16,false),(22,false)]
theorem der_15392 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15392 :=
  CNF.rup_sound cl_15392 [cl_835,cl_836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_835 v h) (hints_cons _ _ _ (inp_836 v h) (by intro d hd; cases hd)))
def cl_15396 : CNF.NClause := [(103,true),(42,true),(41,true),(43,false),(44,false),(45,false)]
theorem der_15396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15396 :=
  CNF.rup_sound cl_15396 [cl_2628,cl_2660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2628 v h) (hints_cons _ _ _ (inp_2660 v h) (by intro d hd; cases hd)))
def cl_15401 : CNF.NClause := [(42,false),(72,false),(11,true),(66,false),(69,false),(80,false),(83,false)]
theorem der_15401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15401 :=
  CNF.rup_sound cl_15401 [cl_5378,cl_5442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5378 v h) (hints_cons _ _ _ (inp_5442 v h) (by intro d hd; cases hd)))
def cl_15402 : CNF.NClause := [(90,true),(8,true),(28,false),(11,true),(19,false),(22,false)]
theorem der_15402 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15402 :=
  CNF.rup_sound cl_15402 [cl_1799,cl_1800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1799 v h) (hints_cons _ _ _ (inp_1800 v h) (by intro d hd; cases hd)))
def cl_15403 : CNF.NClause := [(90,true),(11,true),(28,false),(22,false),(19,false)]
theorem der_15403 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15403 :=
  CNF.rup_sound cl_15403 [cl_15328,cl_15402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15328 v h) (hints_cons _ _ _ (der_15402 v h) (by intro d hd; cases hd)))
def cl_15406 : CNF.NClause := [(103,true),(45,false),(42,true),(43,false),(44,false)]
theorem der_15406 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15406 :=
  CNF.rup_sound cl_15406 [cl_15363,cl_15396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15363 v h) (hints_cons _ _ _ (der_15396 v h) (by intro d hd; cases hd)))
def cl_15408 : CNF.NClause := [(73,true),(18,false),(21,false),(28,false)]
theorem der_15408 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15408 :=
  CNF.rup_sound cl_15408 [cl_15177,cl_15296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15177 v h) (hints_cons _ _ _ (der_15296 v h) (by intro d hd; cases hd)))
def cl_15410 : CNF.NClause := [(92,true),(15,false),(20,false),(25,false)]
theorem der_15410 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15410 :=
  CNF.rup_sound cl_15410 [cl_15180,cl_15273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15180 v h) (hints_cons _ _ _ (der_15273 v h) (by intro d hd; cases hd)))
def cl_15412 : CNF.NClause := [(74,true),(19,false),(29,false),(23,false)]
theorem der_15412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15412 :=
  CNF.rup_sound cl_15412 [cl_15138,cl_15269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15138 v h) (hints_cons _ _ _ (der_15269 v h) (by intro d hd; cases hd)))
def cl_15415 : CNF.NClause := [(76,true),(17,false),(24,false),(27,false)]
theorem der_15415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15415 :=
  CNF.rup_sound cl_15415 [cl_15377,cl_15293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15377 v h) (hints_cons _ _ _ (der_15293 v h) (by intro d hd; cases hd)))
def cl_15417 : CNF.NClause := [(63,true),(14,false),(24,false),(25,false),(19,false)]
theorem der_15417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15417 :=
  CNF.rup_sound cl_15417 [cl_14916,cl_15213] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14916 v h) (hints_cons _ _ _ (der_15213 v h) (by intro d hd; cases hd)))
def cl_15419 : CNF.NClause := [(88,true),(13,false),(21,false),(29,false),(17,false)]
theorem der_15419 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15419 :=
  CNF.rup_sound cl_15419 [cl_14716,cl_15209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14716 v h) (hints_cons _ _ _ (der_15209 v h) (by intro d hd; cases hd)))
def cl_15421 : CNF.NClause := [(72,true),(11,true),(30,false),(12,false),(13,false),(14,false)]
theorem der_15421 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15421 :=
  CNF.rup_sound cl_15421 [cl_643,cl_644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_643 v h) (hints_cons _ _ _ (inp_644 v h) (by intro d hd; cases hd)))
def cl_15423 : CNF.NClause := [(10,true),(75,true),(26,false),(22,false),(16,false)]
theorem der_15423 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15423 :=
  CNF.rup_sound cl_15423 [cl_15241,cl_15280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15241 v h) (hints_cons _ _ _ (der_15280 v h) (by intro d hd; cases hd)))
def cl_15424 : CNF.NClause := [(10,false),(75,true),(22,false),(26,false),(16,false)]
theorem der_15424 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15424 :=
  CNF.rup_sound cl_15424 [cl_15140,cl_15392] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15140 v h) (hints_cons _ _ _ (der_15392 v h) (by intro d hd; cases hd)))
def cl_15425 : CNF.NClause := [(75,true),(16,false),(26,false),(22,false)]
theorem der_15425 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15425 :=
  CNF.rup_sound cl_15425 [cl_15423,cl_15424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15423 v h) (hints_cons _ _ _ (der_15424 v h) (by intro d hd; cases hd)))
def cl_15439 : CNF.NClause := [(64,true),(7,false),(25,false),(12,true),(17,false),(22,false)]
theorem der_15439 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15439 :=
  CNF.rup_sound cl_15439 [cl_133,cl_134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_133 v h) (hints_cons _ _ _ (inp_134 v h) (by intro d hd; cases hd)))
def cl_15443 : CNF.NClause := [(120,true),(54,false),(58,false),(45,false),(47,false),(38,true)]
theorem der_15443 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15443 :=
  CNF.rup_sound cl_15443 [cl_3715,cl_3716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3715 v h) (hints_cons _ _ _ (inp_3716 v h) (by intro d hd; cases hd)))
def cl_15445 : CNF.NClause := [(91,true),(6,false),(26,false),(12,true),(18,false),(24,false)]
theorem der_15445 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15445 :=
  CNF.rup_sound cl_15445 [cl_1861,cl_1862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1861 v h) (hints_cons _ _ _ (inp_1862 v h) (by intro d hd; cases hd)))
def cl_15450 : CNF.NClause := [(87,true),(2,false),(30,false)]
theorem der_15450 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15450 :=
  CNF.rup_sound cl_15450 [cl_14991,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14991 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_15452 : CNF.NClause := [(85,true),(5,false),(27,false),(12,true),(19,false),(21,false)]
theorem der_15452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15452 :=
  CNF.rup_sound cl_15452 [cl_1477,cl_1478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1477 v h) (hints_cons _ _ _ (inp_1478 v h) (by intro d hd; cases hd)))
def cl_15457 : CNF.NClause := [(68,true),(8,false),(29,false),(12,true),(16,false),(20,false)]
theorem der_15457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15457 :=
  CNF.rup_sound cl_15457 [cl_389,cl_390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_389 v h) (hints_cons _ _ _ (inp_390 v h) (by intro d hd; cases hd)))
def cl_15460 : CNF.NClause := [(34,false),(118,true),(32,false),(35,false),(61,false)]
theorem der_15460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15460 :=
  CNF.rup_sound cl_15460 [cl_15133,cl_14910,cl_3586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15133 v h) (hints_cons _ _ _ (der_14910 v h) (hints_cons _ _ _ (inp_3586 v h) (by intro d hd; cases hd))))
def cl_15461 : CNF.NClause := [(34,true),(31,true),(61,false),(35,false),(118,true)]
theorem der_15461 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15461 :=
  CNF.rup_sound cl_15461 [cl_14852,cl_14854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14852 v h) (hints_cons _ _ _ (der_14854 v h) (by intro d hd; cases hd)))
def cl_15462 : CNF.NClause := [(118,true),(61,false),(32,false),(35,false)]
theorem der_15462 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15462 :=
  CNF.rup_sound cl_15462 [cl_15460,cl_15150,cl_15461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15460 v h) (hints_cons _ _ _ (der_15150 v h) (hints_cons _ _ _ (der_15461 v h) (by intro d hd; cases hd))))
def cl_15464 : CNF.NClause := [(34,true),(35,false),(118,true),(61,false)]
theorem der_15464 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15464 :=
  CNF.rup_sound cl_15464 [cl_15150,cl_15461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15150 v h) (hints_cons _ _ _ (der_15461 v h) (by intro d hd; cases hd)))
def cl_15465 : CNF.NClause := [(35,false),(118,true),(61,false)]
theorem der_15465 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15465 :=
  CNF.rup_sound cl_15465 [cl_15462,cl_15464,cl_15133,cl_14910,cl_3588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15462 v h) (hints_cons _ _ _ (der_15464 v h) (hints_cons _ _ _ (der_15133 v h) (hints_cons _ _ _ (der_14910 v h) (hints_cons _ _ _ (inp_3588 v h) (by intro d hd; cases hd))))))
def cl_15466 : CNF.NClause := [(34,false),(118,true),(61,false)]
theorem der_15466 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15466 :=
  CNF.rup_sound cl_15466 [cl_15465,cl_15133,cl_14910,cl_14862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15465 v h) (hints_cons _ _ _ (der_15133 v h) (hints_cons _ _ _ (der_14910 v h) (hints_cons _ _ _ (der_14862 v h) (by intro d hd; cases hd)))))
def cl_15469 : CNF.NClause := [(113,true),(38,true),(39,false),(36,false),(61,false),(37,false)]
theorem der_15469 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15469 :=
  CNF.rup_sound cl_15469 [cl_3269,cl_3285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3269 v h) (hints_cons _ _ _ (inp_3285 v h) (by intro d hd; cases hd)))
def cl_15473 : CNF.NClause := [(82,true),(7,true),(6,true),(5,false),(8,false),(30,false)]
theorem der_15473 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15473 :=
  CNF.rup_sound cl_15473 [cl_15311,cl_1303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15311 v h) (hints_cons _ _ _ (inp_1303 v h) (by intro d hd; cases hd)))
def cl_15474 : CNF.NClause := [(113,true),(39,false),(36,false),(38,true),(61,false),(37,true)]
theorem der_15474 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15474 :=
  CNF.rup_sound cl_15474 [cl_3271,cl_3287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3271 v h) (hints_cons _ _ _ (inp_3287 v h) (by intro d hd; cases hd)))
def cl_15476 : CNF.NClause := [(113,true),(61,false),(36,false),(38,false),(37,true),(39,false)]
theorem der_15476 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15476 :=
  CNF.rup_sound cl_15476 [cl_3267,cl_3283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3267 v h) (hints_cons _ _ _ (inp_3283 v h) (by intro d hd; cases hd)))
def cl_15481 : CNF.NClause := [(91,true),(6,true),(12,true),(26,false),(18,false),(24,false)]
theorem der_15481 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15481 :=
  CNF.rup_sound cl_15481 [cl_1864,cl_1863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1864 v h) (hints_cons _ _ _ (inp_1863 v h) (by intro d hd; cases hd)))
def cl_15482 : CNF.NClause := [(91,true),(12,true),(26,false),(24,false),(18,false)]
theorem der_15482 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15482 :=
  CNF.rup_sound cl_15482 [cl_15445,cl_15481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15445 v h) (hints_cons _ _ _ (der_15481 v h) (by intro d hd; cases hd)))
def cl_15483 : CNF.NClause := [(82,true),(7,false),(8,true),(5,false),(6,true),(30,false)]
theorem der_15483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15483 :=
  CNF.rup_sound cl_15483 [cl_15304,cl_1307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15304 v h) (hints_cons _ _ _ (inp_1307 v h) (by intro d hd; cases hd)))
def cl_15488 : CNF.NClause := [(80,true),(15,false),(29,false),(24,false)]
theorem der_15488 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15488 :=
  CNF.rup_sound cl_15488 [cl_15184,cl_15366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15184 v h) (hints_cons _ _ _ (der_15366 v h) (by intro d hd; cases hd)))
def cl_15493 : CNF.NClause := [(64,true),(7,true),(12,true),(25,false),(17,false),(22,false)]
theorem der_15493 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15493 :=
  CNF.rup_sound cl_15493 [cl_136,cl_135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_136 v h) (hints_cons _ _ _ (inp_135 v h) (by intro d hd; cases hd)))
def cl_15494 : CNF.NClause := [(64,true),(12,true),(25,false),(22,false),(17,false)]
theorem der_15494 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15494 :=
  CNF.rup_sound cl_15494 [cl_15439,cl_15493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15439 v h) (hints_cons _ _ _ (der_15493 v h) (by intro d hd; cases hd)))
def cl_15495 : CNF.NClause := [(69,true),(11,false),(20,false),(27,false),(18,false)]
theorem der_15495 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15495 :=
  CNF.rup_sound cl_15495 [cl_14922,cl_15205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14922 v h) (hints_cons _ _ _ (der_15205 v h) (by intro d hd; cases hd)))
def cl_15502 : CNF.NClause := [(68,true),(4,false),(12,true),(16,false),(20,false),(29,false)]
theorem der_15502 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15502 :=
  CNF.rup_sound cl_15502 [cl_15457,cl_391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15457 v h) (hints_cons _ _ _ (inp_391 v h) (by intro d hd; cases hd)))
def cl_15503 : CNF.NClause := [(81,true),(1,false),(28,false),(12,true),(15,false),(23,false)]
theorem der_15503 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15503 :=
  CNF.rup_sound cl_15503 [cl_1221,cl_1223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1221 v h) (hints_cons _ _ _ (inp_1223 v h) (by intro d hd; cases hd)))
def cl_15505 : CNF.NClause := [(1,true),(81,true),(28,false),(12,true),(15,false),(23,false)]
theorem der_15505 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15505 :=
  CNF.rup_sound cl_15505 [cl_1224,cl_1222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1224 v h) (hints_cons _ _ _ (inp_1222 v h) (by intro d hd; cases hd)))
def cl_15506 : CNF.NClause := [(81,true),(12,true),(28,false),(23,false),(15,false)]
theorem der_15506 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15506 :=
  CNF.rup_sound cl_15506 [cl_15503,cl_15505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15503 v h) (hints_cons _ _ _ (der_15505 v h) (by intro d hd; cases hd)))
def cl_15512 : CNF.NClause := [(72,true),(11,false),(30,false),(12,true),(13,false),(14,false)]
theorem der_15512 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15512 :=
  CNF.rup_sound cl_15512 [cl_645,cl_646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_645 v h) (hints_cons _ _ _ (inp_646 v h) (by intro d hd; cases hd)))
def cl_15515 : CNF.NClause := [(68,true),(8,true),(12,true),(29,false),(16,false),(20,false)]
theorem der_15515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15515 :=
  CNF.rup_sound cl_15515 [cl_392,cl_15502] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_392 v h) (hints_cons _ _ _ (der_15502 v h) (by intro d hd; cases hd)))
def cl_15516 : CNF.NClause := [(68,true),(12,true),(29,false),(20,false),(16,false)]
theorem der_15516 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15516 :=
  CNF.rup_sound cl_15516 [cl_15457,cl_15515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15457 v h) (hints_cons _ _ _ (der_15515 v h) (by intro d hd; cases hd)))
def cl_15530 : CNF.NClause := [(103,true),(42,true),(61,false),(43,true),(44,false),(45,false)]
theorem der_15530 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15530 :=
  CNF.rup_sound cl_15530 [cl_2631,cl_2632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2631 v h) (hints_cons _ _ _ (inp_2632 v h) (by intro d hd; cases hd)))
def cl_15535 : CNF.NClause := [(35,true),(118,true),(32,false),(61,false),(34,true),(31,true)]
theorem der_15535 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15535 :=
  CNF.rup_sound cl_15535 [cl_3614,cl_14864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3614 v h) (hints_cons _ _ _ (der_14864 v h) (by intro d hd; cases hd)))
def cl_15536 : CNF.NClause := [(118,true),(32,false),(61,false)]
theorem der_15536 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15536 :=
  CNF.rup_sound cl_15536 [cl_15465,cl_15466,cl_15150,cl_15535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15465 v h) (hints_cons _ _ _ (der_15466 v h) (hints_cons _ _ _ (der_15150 v h) (hints_cons _ _ _ (der_15535 v h) (by intro d hd; cases hd)))))
def cl_15538 : CNF.NClause := [(66,true),(16,false),(21,false),(25,false)]
theorem der_15538 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15538 :=
  CNF.rup_sound cl_15538 [cl_15081,cl_15374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15081 v h) (hints_cons _ _ _ (der_15374 v h) (by intro d hd; cases hd)))
def cl_15543 : CNF.NClause := [(40,true),(106,true),(34,false),(57,false),(47,false),(53,false)]
theorem der_15543 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15543 :=
  CNF.rup_sound cl_15543 [cl_2819,cl_2823] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2819 v h) (hints_cons _ _ _ (inp_2823 v h) (by intro d hd; cases hd)))
def cl_15544 : CNF.NClause := [(40,false),(106,true),(34,false),(47,false),(57,false),(53,false)]
theorem der_15544 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15544 :=
  CNF.rup_sound cl_15544 [cl_2817,cl_2821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2817 v h) (hints_cons _ _ _ (inp_2821 v h) (by intro d hd; cases hd)))
def cl_15545 : CNF.NClause := [(106,true),(53,false),(34,false),(57,false),(47,false)]
theorem der_15545 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15545 :=
  CNF.rup_sound cl_15545 [cl_15543,cl_15544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15543 v h) (hints_cons _ _ _ (der_15544 v h) (by intro d hd; cases hd)))
def cl_15546 : CNF.NClause := [(111,true),(34,false),(55,false),(60,false),(42,false),(46,false)]
theorem der_15546 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15546 :=
  CNF.rup_sound cl_15546 [cl_3137,cl_3139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3137 v h) (hints_cons _ _ _ (inp_3139 v h) (by intro d hd; cases hd)))
def cl_15548 : CNF.NClause := [(83,true),(17,false),(23,false),(26,false)]
theorem der_15548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15548 :=
  CNF.rup_sound cl_15548 [cl_15108,cl_15384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15108 v h) (hints_cons _ _ _ (der_15384 v h) (by intro d hd; cases hd)))
def cl_15549 : CNF.NClause := [(69,true),(18,false),(20,false),(27,false)]
theorem der_15549 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15549 :=
  CNF.rup_sound cl_15549 [cl_15495,cl_15371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15495 v h) (hints_cons _ _ _ (der_15371 v h) (by intro d hd; cases hd)))
def cl_15550 : CNF.NClause := [(6,false),(5,false),(9,true),(30,false),(8,false),(82,true)]
theorem der_15550 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15550 :=
  CNF.rup_sound cl_15550 [cl_1297,cl_1301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1297 v h) (hints_cons _ _ _ (inp_1301 v h) (by intro d hd; cases hd)))
def cl_15554 : CNF.NClause := [(72,true),(11,true),(30,false),(12,true),(13,false),(14,false)]
theorem der_15554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15554 :=
  CNF.rup_sound cl_15554 [cl_647,cl_648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_647 v h) (hints_cons _ _ _ (inp_648 v h) (by intro d hd; cases hd)))
def cl_15555 : CNF.NClause := [(72,true),(12,true),(30,false),(14,false),(13,false)]
theorem der_15555 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15555 :=
  CNF.rup_sound cl_15555 [cl_15512,cl_15554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15512 v h) (hints_cons _ _ _ (der_15554 v h) (by intro d hd; cases hd)))
def cl_15557 : CNF.NClause := [(5,false),(7,false),(30,false),(8,false),(82,true),(9,true)]
theorem der_15557 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15557 :=
  CNF.rup_sound cl_15557 [cl_1299,cl_15550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1299 v h) (hints_cons _ _ _ (der_15550 v h) (by intro d hd; cases hd)))
def cl_15559 : CNF.NClause := [(9,false),(8,true),(30,false),(82,true)]
theorem der_15559 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15559 :=
  CNF.rup_sound cl_15559 [cl_15304,cl_15298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15304 v h) (hints_cons _ _ _ (der_15298 v h) (by intro d hd; cases hd)))
def cl_15560 : CNF.NClause := [(6,false),(8,true),(30,false),(82,true)]
theorem der_15560 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15560 :=
  CNF.rup_sound cl_15560 [cl_15223,cl_15559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15223 v h) (hints_cons _ _ _ (der_15559 v h) (by intro d hd; cases hd)))
def cl_15574 : CNF.NClause := [(113,true),(61,false),(38,false),(40,false),(39,false),(36,false)]
theorem der_15574 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15574 :=
  CNF.rup_sound cl_15574 [cl_3265,cl_15476] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3265 v h) (hints_cons _ _ _ (der_15476 v h) (by intro d hd; cases hd)))
def cl_15587 : CNF.NClause := [(38,false),(36,false),(37,false),(39,true),(113,true),(61,false)]
theorem der_15587 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15587 :=
  CNF.rup_sound cl_15587 [cl_3273,cl_3289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3273 v h) (hints_cons _ _ _ (inp_3289 v h) (by intro d hd; cases hd)))
def cl_15588 : CNF.NClause := [(38,true),(36,false),(61,false),(39,true),(37,false),(113,true)]
theorem der_15588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15588 :=
  CNF.rup_sound cl_15588 [cl_3277,cl_3293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3277 v h) (hints_cons _ _ _ (inp_3293 v h) (by intro d hd; cases hd)))
def cl_15589 : CNF.NClause := [(36,false),(113,true),(37,false),(39,true),(61,false)]
theorem der_15589 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15589 :=
  CNF.rup_sound cl_15589 [cl_15587,cl_15588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15587 v h) (hints_cons _ _ _ (der_15588 v h) (by intro d hd; cases hd)))
def cl_15592 : CNF.NClause := [(7,false),(6,false),(30,false),(82,true),(8,false),(9,true)]
theorem der_15592 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15592 :=
  CNF.rup_sound cl_15592 [cl_1298,cl_15557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1298 v h) (hints_cons _ _ _ (der_15557 v h) (by intro d hd; cases hd)))
def cl_15594 : CNF.NClause := [(9,true),(6,false),(82,true),(30,false),(8,false)]
theorem der_15594 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15594 :=
  CNF.rup_sound cl_15594 [cl_15550,cl_15592,cl_1302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15550 v h) (hints_cons _ _ _ (der_15592 v h) (hints_cons _ _ _ (inp_1302 v h) (by intro d hd; cases hd))))
def cl_15595 : CNF.NClause := [(6,false),(82,true),(30,false)]
theorem der_15595 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15595 :=
  CNF.rup_sound cl_15595 [cl_15560,cl_15311,cl_15594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15560 v h) (hints_cons _ _ _ (der_15311 v h) (hints_cons _ _ _ (der_15594 v h) (by intro d hd; cases hd))))
def cl_15596 : CNF.NClause := [(7,true),(8,false),(82,true),(30,false)]
theorem der_15596 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15596 :=
  CNF.rup_sound cl_15596 [cl_15311,cl_15595,cl_15473,cl_1304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15311 v h) (hints_cons _ _ _ (der_15595 v h) (hints_cons _ _ _ (der_15473 v h) (hints_cons _ _ _ (inp_1304 v h) (by intro d hd; cases hd)))))
def cl_15597 : CNF.NClause := [(7,false),(9,true),(82,true),(6,true),(30,false),(8,false)]
theorem der_15597 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15597 :=
  CNF.rup_sound cl_15597 [cl_1300,cl_15557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1300 v h) (hints_cons _ _ _ (der_15557 v h) (by intro d hd; cases hd)))
def cl_15598 : CNF.NClause := [(8,false),(82,true),(30,false)]
theorem der_15598 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15598 :=
  CNF.rup_sound cl_15598 [cl_15595,cl_15311,cl_15596,cl_15597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15595 v h) (hints_cons _ _ _ (der_15311 v h) (hints_cons _ _ _ (der_15596 v h) (hints_cons _ _ _ (der_15597 v h) (by intro d hd; cases hd)))))
def cl_15639 : CNF.NClause := [(300,true),(296,true),(297,true),(294,true),(293,true),(292,true),(291,true),(290,true),(288,false),(287,true),(286,true),(285,true),(282,true),(281,true),(279,true)]
theorem der_15639 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15639 :=
  CNF.rup_sound cl_15639 [cl_9000,cl_9058,cl_9073,cl_9006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_9000 v h) (hints_cons _ _ _ (inp_9058 v h) (hints_cons _ _ _ (inp_9073 v h) (hints_cons _ _ _ (inp_9006 v h) (by intro d hd; cases hd)))))
def cl_15920 : CNF.NClause := [(304,true),(303,true),(302,true),(299,true),(293,true),(292,true),(291,true),(288,false),(287,true),(286,true),(285,true),(283,true),(282,true),(280,true),(279,true)]
theorem der_15920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_15920 :=
  CNF.rup_sound cl_15920 [cl_8918,cl_8908,cl_9072,cl_8954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8918 v h) (hints_cons _ _ _ (inp_8908 v h) (hints_cons _ _ _ (inp_9072 v h) (hints_cons _ _ _ (inp_8954 v h) (by intro d hd; cases hd)))))
def cl_16753 : CNF.NClause := [(148,true),(147,true),(142,true),(151,true),(136,true),(135,true),(134,true),(132,true),(130,true),(129,true),(128,true),(125,true),(124,false)]
theorem der_16753 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_16753 :=
  CNF.rup_sound cl_16753 [cl_8054,cl_8147,cl_8094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8054 v h) (hints_cons _ _ _ (inp_8147 v h) (hints_cons _ _ _ (inp_8094 v h) (by intro d hd; cases hd))))
def cl_17601 : CNF.NClause := [(7,false),(9,true),(30,true),(6,false),(8,false),(82,true)]
theorem der_17601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17601 :=
  CNF.rup_sound cl_17601 [cl_1329,cl_1330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1329 v h) (hints_cons _ _ _ (inp_1330 v h) (by intro d hd; cases hd)))
def cl_17602 : CNF.NClause := [(7,true),(9,true),(30,true),(6,false),(8,false),(82,true)]
theorem der_17602 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17602 :=
  CNF.rup_sound cl_17602 [cl_1334,cl_1333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1334 v h) (hints_cons _ _ _ (inp_1333 v h) (by intro d hd; cases hd)))
def cl_17603 : CNF.NClause := [(9,true),(8,false),(30,true),(6,false),(82,true)]
theorem der_17603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17603 :=
  CNF.rup_sound cl_17603 [cl_17601,cl_17602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17601 v h) (hints_cons _ _ _ (der_17602 v h) (by intro d hd; cases hd)))
def cl_17604 : CNF.NClause := [(7,true),(8,false),(30,true),(6,false),(82,true),(9,false)]
theorem der_17604 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17604 :=
  CNF.rup_sound cl_17604 [cl_1317,cl_1318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1317 v h) (hints_cons _ _ _ (inp_1318 v h) (by intro d hd; cases hd)))
def cl_17605 : CNF.NClause := [(7,false),(8,false),(30,true),(6,false),(82,true),(9,false)]
theorem der_17605 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17605 :=
  CNF.rup_sound cl_17605 [cl_1314,cl_1313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1314 v h) (hints_cons _ _ _ (inp_1313 v h) (by intro d hd; cases hd)))
def cl_17606 : CNF.NClause := [(8,false),(9,false),(30,true),(6,false),(82,true)]
theorem der_17606 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17606 :=
  CNF.rup_sound cl_17606 [cl_17604,cl_17605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17604 v h) (hints_cons _ _ _ (der_17605 v h) (by intro d hd; cases hd)))
def cl_17607 : CNF.NClause := [(8,false),(6,false),(30,true),(82,true)]
theorem der_17607 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17607 :=
  CNF.rup_sound cl_17607 [cl_17603,cl_17606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17603 v h) (hints_cons _ _ _ (der_17606 v h) (by intro d hd; cases hd)))
def cl_17608 : CNF.NClause := [(7,false),(9,false),(30,true),(6,false),(8,true),(82,true)]
theorem der_17608 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17608 :=
  CNF.rup_sound cl_17608 [cl_1321,cl_1322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1321 v h) (hints_cons _ _ _ (inp_1322 v h) (by intro d hd; cases hd)))
def cl_17609 : CNF.NClause := [(7,true),(9,false),(30,true),(6,false),(8,true),(82,true)]
theorem der_17609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17609 :=
  CNF.rup_sound cl_17609 [cl_1325,cl_1326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1325 v h) (hints_cons _ _ _ (inp_1326 v h) (by intro d hd; cases hd)))
def cl_17610 : CNF.NClause := [(9,false),(6,false),(30,true),(82,true),(8,true)]
theorem der_17610 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17610 :=
  CNF.rup_sound cl_17610 [cl_17608,cl_17609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17608 v h) (hints_cons _ _ _ (der_17609 v h) (by intro d hd; cases hd)))
def cl_17611 : CNF.NClause := [(47,false),(66,true),(89,true),(68,true),(75,true),(77,true),(84,true)]
theorem der_17611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17611 :=
  CNF.rup_sound cl_17611 [cl_6143,cl_6144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6143 v h) (hints_cons _ _ _ (inp_6144 v h) (by intro d hd; cases hd)))
def cl_17612 : CNF.NClause := [(46,false),(78,true),(77,true),(92,true),(79,true),(80,true),(81,true)]
theorem der_17612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17612 :=
  CNF.rup_sound cl_17612 [cl_6015,cl_6016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6015 v h) (hints_cons _ _ _ (inp_6016 v h) (by intro d hd; cases hd)))
def cl_17613 : CNF.NClause := [(41,false),(74,true),(72,true),(73,true),(92,true),(75,true),(76,true)]
theorem der_17613 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17613 :=
  CNF.rup_sound cl_17613 [cl_5375,cl_5376] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5375 v h) (hints_cons _ _ _ (inp_5376 v h) (by intro d hd; cases hd)))
def cl_17614 : CNF.NClause := [(4,true),(15,true),(6,false),(78,true),(27,true),(22,false)]
theorem der_17614 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17614 :=
  CNF.rup_sound cl_17614 [cl_1066,cl_1070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1066 v h) (hints_cons _ _ _ (inp_1070 v h) (by intro d hd; cases hd)))
def cl_17615 : CNF.NClause := [(4,false),(10,true),(28,false),(73,true),(21,true),(7,true)]
theorem der_17615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17615 :=
  CNF.rup_sound cl_17615 [cl_727,cl_735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_727 v h) (hints_cons _ _ _ (inp_735 v h) (by intro d hd; cases hd)))
def cl_17616 : CNF.NClause := [(4,false),(15,true),(78,true),(6,false),(27,true),(22,false)]
theorem der_17616 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17616 :=
  CNF.rup_sound cl_17616 [cl_1065,cl_1069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1065 v h) (hints_cons _ _ _ (inp_1069 v h) (by intro d hd; cases hd)))
def cl_17617 : CNF.NClause := [(15,true),(78,true),(6,false),(22,false),(27,true)]
theorem der_17617 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17617 :=
  CNF.rup_sound cl_17617 [cl_17614,cl_17616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17614 v h) (hints_cons _ _ _ (der_17616 v h) (by intro d hd; cases hd)))
def cl_17618 : CNF.NClause := [(15,false),(23,true),(9,true),(12,false),(81,true),(28,false)]
theorem der_17618 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17618 :=
  CNF.rup_sound cl_17618 [cl_1235,cl_1236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1235 v h) (hints_cons _ _ _ (inp_1236 v h) (by intro d hd; cases hd)))
def cl_17619 : CNF.NClause := [(15,false),(81,true),(28,false),(12,false),(9,true)]
theorem der_17619 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17619 :=
  CNF.rup_sound cl_17619 [cl_15193,cl_17618] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15193 v h) (hints_cons _ _ _ (der_17618 v h) (by intro d hd; cases hd)))
def cl_17620 : CNF.NClause := [(23,true),(81,true),(9,true),(12,false),(28,false),(15,true)]
theorem der_17620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17620 :=
  CNF.rup_sound cl_17620 [cl_1243,cl_1244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1243 v h) (hints_cons _ _ _ (inp_1244 v h) (by intro d hd; cases hd)))
def cl_17621 : CNF.NClause := [(23,false),(81,true),(9,true),(12,false),(28,false),(15,true)]
theorem der_17621 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17621 :=
  CNF.rup_sound cl_17621 [cl_1227,cl_1228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1227 v h) (hints_cons _ _ _ (inp_1228 v h) (by intro d hd; cases hd)))
def cl_17622 : CNF.NClause := [(81,true),(15,true),(9,true),(12,false),(28,false)]
theorem der_17622 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17622 :=
  CNF.rup_sound cl_17622 [cl_17620,cl_17621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17620 v h) (hints_cons _ _ _ (der_17621 v h) (by intro d hd; cases hd)))
def cl_17623 : CNF.NClause := [(81,true),(28,false),(9,true),(12,false)]
theorem der_17623 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17623 :=
  CNF.rup_sound cl_17623 [cl_17619,cl_17622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17619 v h) (hints_cons _ _ _ (der_17622 v h) (by intro d hd; cases hd)))
def cl_17624 : CNF.NClause := [(10,false),(73,true),(4,false),(7,true),(28,false),(21,true)]
theorem der_17624 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17624 :=
  CNF.rup_sound cl_17624 [cl_723,cl_731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_723 v h) (hints_cons _ _ _ (inp_731 v h) (by intro d hd; cases hd)))
def cl_17625 : CNF.NClause := [(73,true),(4,false),(28,false),(7,true),(21,true)]
theorem der_17625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17625 :=
  CNF.rup_sound cl_17625 [cl_17615,cl_17624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17615 v h) (hints_cons _ _ _ (der_17624 v h) (by intro d hd; cases hd)))
def cl_17626 : CNF.NClause := [(10,false),(13,true),(30,true),(11,false),(12,false),(72,true)]
theorem der_17626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17626 :=
  CNF.rup_sound cl_17626 [cl_681,cl_697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_681 v h) (hints_cons _ _ _ (inp_697 v h) (by intro d hd; cases hd)))
def cl_17627 : CNF.NClause := [(10,true),(13,true),(11,false),(12,false),(72,true),(30,true)]
theorem der_17627 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17627 :=
  CNF.rup_sound cl_17627 [cl_682,cl_698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_682 v h) (hints_cons _ _ _ (inp_698 v h) (by intro d hd; cases hd)))
def cl_17628 : CNF.NClause := [(13,true),(72,true),(30,true),(11,false),(12,false)]
theorem der_17628 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17628 :=
  CNF.rup_sound cl_17628 [cl_17626,cl_17627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17626 v h) (hints_cons _ _ _ (der_17627 v h) (by intro d hd; cases hd)))
def cl_17629 : CNF.NClause := [(10,true),(72,true),(11,false),(12,false),(30,true),(13,false)]
theorem der_17629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17629 :=
  CNF.rup_sound cl_17629 [cl_674,cl_690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_674 v h) (hints_cons _ _ _ (inp_690 v h) (by intro d hd; cases hd)))
def cl_17630 : CNF.NClause := [(10,false),(72,true),(30,true),(11,false),(12,false),(13,false)]
theorem der_17630 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17630 :=
  CNF.rup_sound cl_17630 [cl_673,cl_689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_673 v h) (hints_cons _ _ _ (inp_689 v h) (by intro d hd; cases hd)))
def cl_17631 : CNF.NClause := [(72,true),(13,false),(11,false),(12,false),(30,true)]
theorem der_17631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17631 :=
  CNF.rup_sound cl_17631 [cl_17629,cl_17630] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17629 v h) (hints_cons _ _ _ (der_17630 v h) (by intro d hd; cases hd)))
def cl_17632 : CNF.NClause := [(72,true),(12,false),(30,true),(11,false)]
theorem der_17632 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17632 :=
  CNF.rup_sound cl_17632 [cl_17628,cl_17631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17628 v h) (hints_cons _ _ _ (der_17631 v h) (by intro d hd; cases hd)))
def cl_17633 : CNF.NClause := [(16,true),(66,true),(6,false),(11,false),(1,true),(21,true)]
theorem der_17633 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17633 :=
  CNF.rup_sound cl_17633 [cl_282,cl_314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_282 v h) (hints_cons _ _ _ (inp_314 v h) (by intro d hd; cases hd)))
def cl_17634 : CNF.NClause := [(16,false),(66,true),(6,false),(11,false),(1,true),(21,true)]
theorem der_17634 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17634 :=
  CNF.rup_sound cl_17634 [cl_274,cl_306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_274 v h) (hints_cons _ _ _ (inp_306 v h) (by intro d hd; cases hd)))
def cl_17635 : CNF.NClause := [(66,true),(1,true),(6,false),(11,false),(21,true)]
theorem der_17635 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17635 :=
  CNF.rup_sound cl_17635 [cl_17633,cl_17634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17633 v h) (hints_cons _ _ _ (der_17634 v h) (by intro d hd; cases hd)))
def cl_17636 : CNF.NClause := [(16,false),(89,true),(23,false),(27,true),(7,true),(14,true)]
theorem der_17636 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17636 :=
  CNF.rup_sound cl_17636 [cl_1768,cl_1767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1768 v h) (hints_cons _ _ _ (inp_1767 v h) (by intro d hd; cases hd)))
def cl_17637 : CNF.NClause := [(17,false),(76,true),(1,true),(27,true),(10,false),(8,true)]
theorem der_17637 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17637 :=
  CNF.rup_sound cl_17637 [cl_932,cl_948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_932 v h) (hints_cons _ _ _ (inp_948 v h) (by intro d hd; cases hd)))
def cl_17638 : CNF.NClause := [(16,false),(84,true),(5,true),(13,false),(28,false),(24,true)]
theorem der_17638 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17638 :=
  CNF.rup_sound cl_17638 [cl_1427,cl_1428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1427 v h) (hints_cons _ _ _ (inp_1428 v h) (by intro d hd; cases hd)))
def cl_17639 : CNF.NClause := [(26,true),(16,false),(9,true),(75,true),(10,false),(22,false)]
theorem der_17639 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17639 :=
  CNF.rup_sound cl_17639 [cl_868,cl_867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_868 v h) (hints_cons _ _ _ (inp_867 v h) (by intro d hd; cases hd)))
def cl_17640 : CNF.NClause := [(16,false),(10,false),(22,false),(75,true),(9,true)]
theorem der_17640 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17640 :=
  CNF.rup_sound cl_17640 [cl_15425,cl_17639] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15425 v h) (hints_cons _ _ _ (der_17639 v h) (by intro d hd; cases hd)))
def cl_17641 : CNF.NClause := [(26,true),(16,true),(22,false),(10,false),(9,true),(75,true)]
theorem der_17641 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17641 :=
  CNF.rup_sound cl_17641 [cl_875,cl_876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_875 v h) (hints_cons _ _ _ (inp_876 v h) (by intro d hd; cases hd)))
def cl_17642 : CNF.NClause := [(26,false),(10,false),(9,true),(75,true),(22,false),(16,true)]
theorem der_17642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17642 :=
  CNF.rup_sound cl_17642 [cl_844,cl_843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_844 v h) (hints_cons _ _ _ (inp_843 v h) (by intro d hd; cases hd)))
def cl_17643 : CNF.NClause := [(16,true),(10,false),(22,false),(75,true),(9,true)]
theorem der_17643 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17643 :=
  CNF.rup_sound cl_17643 [cl_17641,cl_17642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17641 v h) (hints_cons _ _ _ (der_17642 v h) (by intro d hd; cases hd)))
def cl_17644 : CNF.NClause := [(10,false),(22,false),(9,true),(75,true)]
theorem der_17644 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17644 :=
  CNF.rup_sound cl_17644 [cl_17640,cl_17643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17640 v h) (hints_cons _ _ _ (der_17643 v h) (by intro d hd; cases hd)))
def cl_17645 : CNF.NClause := [(26,false),(16,true),(9,true),(75,true),(10,true),(22,false)]
theorem der_17645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17645 :=
  CNF.rup_sound cl_17645 [cl_848,cl_847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_848 v h) (hints_cons _ _ _ (inp_847 v h) (by intro d hd; cases hd)))
def cl_17647 : CNF.NClause := [(119,true),(44,false),(31,false),(52,true),(48,false),(40,true)]
theorem der_17647 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17647 :=
  CNF.rup_sound cl_17647 [cl_3667,cl_3699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3667 v h) (hints_cons _ _ _ (inp_3699 v h) (by intro d hd; cases hd)))
def cl_17649 : CNF.NClause := [(119,true),(48,false),(31,false),(40,true),(44,true),(52,true)]
theorem der_17649 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17649 :=
  CNF.rup_sound cl_17649 [cl_3671,cl_3703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3671 v h) (hints_cons _ _ _ (inp_3703 v h) (by intro d hd; cases hd)))
def cl_17652 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,false),(21,true)]
theorem der_17652 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17652 :=
  CNF.rup_sound cl_17652 [cl_1683,cl_1715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1683 v h) (hints_cons _ _ _ (inp_1715 v h) (by intro d hd; cases hd)))
def cl_17654 : CNF.NClause := [(86,true),(18,false),(1,true),(5,true),(22,false),(14,true)]
theorem der_17654 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17654 :=
  CNF.rup_sound cl_17654 [cl_1576,cl_1544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1576 v h) (hints_cons _ _ _ (inp_1544 v h) (by intro d hd; cases hd)))
def cl_17656 : CNF.NClause := [(69,true),(18,false),(9,true),(11,false),(2,true),(27,true)]
theorem der_17656 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17656 :=
  CNF.rup_sound cl_17656 [cl_484,cl_500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_484 v h) (hints_cons _ _ _ (inp_500 v h) (by intro d hd; cases hd)))
def cl_17658 : CNF.NClause := [(62,true),(25,false),(30,true),(27,true),(26,true),(28,false)]
theorem der_17658 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17658 :=
  CNF.rup_sound cl_17658 [cl_39,cl_55] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_39 v h) (hints_cons _ _ _ (inp_55 v h) (by intro d hd; cases hd)))
def cl_17660 : CNF.NClause := [(67,true),(23,false),(24,false),(21,true),(30,true),(22,false)]
theorem der_17660 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17660 :=
  CNF.rup_sound cl_17660 [cl_356,cl_355] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_356 v h) (hints_cons _ _ _ (inp_355 v h) (by intro d hd; cases hd)))
def cl_17662 : CNF.NClause := [(68,true),(20,false),(4,false),(8,true),(12,false),(16,true)]
theorem der_17662 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17662 :=
  CNF.rup_sound cl_17662 [cl_395,cl_427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_395 v h) (hints_cons _ _ _ (inp_427 v h) (by intro d hd; cases hd)))
def cl_17663 : CNF.NClause := [(20,true),(68,true),(4,false),(8,true),(12,false),(16,true)]
theorem der_17663 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17663 :=
  CNF.rup_sound cl_17663 [cl_411,cl_443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_411 v h) (hints_cons _ _ _ (inp_443 v h) (by intro d hd; cases hd)))
def cl_17664 : CNF.NClause := [(68,true),(4,false),(16,true),(8,true),(12,false)]
theorem der_17664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17664 :=
  CNF.rup_sound cl_17664 [cl_17662,cl_17663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17662 v h) (hints_cons _ _ _ (der_17663 v h) (by intro d hd; cases hd)))
def cl_17665 : CNF.NClause := [(80,true),(15,false),(3,true),(11,false),(7,true),(24,false)]
theorem der_17665 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17665 :=
  CNF.rup_sound cl_17665 [cl_1188,cl_15488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1188 v h) (hints_cons _ _ _ (der_15488 v h) (by intro d hd; cases hd)))
def cl_17666 : CNF.NClause := [(74,true),(23,false),(6,false),(2,true),(19,true),(10,true)]
theorem der_17666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17666 :=
  CNF.rup_sound cl_17666 [cl_782,cl_814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_782 v h) (hints_cons _ _ _ (inp_814 v h) (by intro d hd; cases hd)))
def cl_17675 : CNF.NClause := [(92,true),(0,false),(20,false),(15,false),(10,true),(5,true)]
theorem der_17675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17675 :=
  CNF.rup_sound cl_17675 [cl_15410,cl_1959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15410 v h) (hints_cons _ _ _ (inp_1959 v h) (by intro d hd; cases hd)))
def cl_17682 : CNF.NClause := [(15,true),(80,true),(3,true),(11,false),(7,true),(24,false)]
theorem der_17682 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17682 :=
  CNF.rup_sound cl_17682 [cl_1164,cl_1196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1164 v h) (hints_cons _ _ _ (inp_1196 v h) (by intro d hd; cases hd)))
def cl_17683 : CNF.NClause := [(80,true),(24,false),(3,true),(11,false),(7,true)]
theorem der_17683 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17683 :=
  CNF.rup_sound cl_17683 [cl_17665,cl_17682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17665 v h) (hints_cons _ _ _ (der_17682 v h) (by intro d hd; cases hd)))
def cl_17687 : CNF.NClause := [(92,true),(20,false),(5,true),(0,false),(15,true),(10,true)]
theorem der_17687 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17687 :=
  CNF.rup_sound cl_17687 [cl_1967,cl_1935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1967 v h) (hints_cons _ _ _ (inp_1935 v h) (by intro d hd; cases hd)))
def cl_17696 : CNF.NClause := [(92,true),(0,true),(20,false),(15,false),(10,true),(5,true)]
theorem der_17696 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17696 :=
  CNF.rup_sound cl_17696 [cl_15410,cl_1960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15410 v h) (hints_cons _ _ _ (inp_1960 v h) (by intro d hd; cases hd)))
def cl_17717 : CNF.NClause := [(92,true),(0,false),(5,true),(20,true),(10,true),(15,false)]
theorem der_17717 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17717 :=
  CNF.rup_sound cl_17717 [cl_1975,cl_1943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1975 v h) (hints_cons _ _ _ (inp_1943 v h) (by intro d hd; cases hd)))
def cl_17775 : CNF.NClause := [(86,true),(18,true),(22,false),(1,true),(5,true),(14,false)]
theorem der_17775 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17775 :=
  CNF.rup_sound cl_17775 [cl_1580,cl_1548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1580 v h) (hints_cons _ _ _ (inp_1548 v h) (by intro d hd; cases hd)))
def cl_17777 : CNF.NClause := [(74,true),(23,false),(2,false),(10,true),(6,false),(19,true)]
theorem der_17777 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17777 :=
  CNF.rup_sound cl_17777 [cl_781,cl_813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_781 v h) (hints_cons _ _ _ (inp_813 v h) (by intro d hd; cases hd)))
def cl_17790 : CNF.NClause := [(77,true),(15,false),(30,true),(16,true),(17,false),(19,true)]
theorem der_17790 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17790 :=
  CNF.rup_sound cl_17790 [cl_1019,cl_1011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1019 v h) (hints_cons _ _ _ (inp_1011 v h) (by intro d hd; cases hd)))
def cl_17791 : CNF.NClause := [(68,true),(4,true),(20,false),(12,false),(8,true),(16,true)]
theorem der_17791 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17791 :=
  CNF.rup_sound cl_17791 [cl_396,cl_428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_396 v h) (hints_cons _ _ _ (inp_428 v h) (by intro d hd; cases hd)))
def cl_17802 : CNF.NClause := [(74,true),(23,true),(2,false),(10,true),(6,false),(19,true)]
theorem der_17802 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17802 :=
  CNF.rup_sound cl_17802 [cl_797,cl_829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_797 v h) (hints_cons _ _ _ (inp_829 v h) (by intro d hd; cases hd)))
def cl_17810 : CNF.NClause := [(88,true),(0,true),(9,true),(13,false),(17,false),(21,true)]
theorem der_17810 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17810 :=
  CNF.rup_sound cl_17810 [cl_1684,cl_1716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1684 v h) (hints_cons _ _ _ (inp_1716 v h) (by intro d hd; cases hd)))
def cl_17820 : CNF.NClause := [(105,true),(33,false),(50,true),(41,true),(37,true),(54,false)]
theorem der_17820 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17820 :=
  CNF.rup_sound cl_17820 [cl_2767,cl_2799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2767 v h) (hints_cons _ _ _ (inp_2799 v h) (by intro d hd; cases hd)))
def cl_17828 : CNF.NClause := [(37,false),(78,false),(82,true),(6,false),(66,false),(74,false),(91,false)]
theorem der_17828 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17828 :=
  CNF.rup_sound cl_17828 [cl_4769,cl_4773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4769 v h) (hints_cons _ _ _ (inp_4773 v h) (by intro d hd; cases hd)))
def cl_17829 : CNF.NClause := [(70,true),(20,false),(6,false),(3,true),(17,false),(28,false)]
theorem der_17829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17829 :=
  CNF.rup_sound cl_17829 [cl_518,cl_15155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_518 v h) (hints_cons _ _ _ (der_15155 v h) (by intro d hd; cases hd)))
def cl_17831 : CNF.NClause := [(64,true),(2,false),(17,false),(22,false),(12,false),(7,true)]
theorem der_17831 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17831 :=
  CNF.rup_sound cl_17831 [cl_15175,cl_163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15175 v h) (hints_cons _ _ _ (inp_163 v h) (by intro d hd; cases hd)))
def cl_17832 : CNF.NClause := [(50,false),(90,false),(77,false),(74,false),(19,true),(71,false),(85,true)]
theorem der_17832 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17832 :=
  CNF.rup_sound cl_17832 [cl_6434,cl_6436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6434 v h) (hints_cons _ _ _ (inp_6436 v h) (by intro d hd; cases hd)))
def cl_17834 : CNF.NClause := [(99,true),(39,true),(51,false),(43,true),(47,true),(35,false)]
theorem der_17834 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17834 :=
  CNF.rup_sound cl_17834 [cl_2383,cl_2415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2383 v h) (hints_cons _ _ _ (inp_2415 v h) (by intro d hd; cases hd)))
def cl_17836 : CNF.NClause := [(79,true),(15,false),(8,true),(26,true),(2,false),(21,true)]
theorem der_17836 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17836 :=
  CNF.rup_sound cl_17836 [cl_1143,cl_1139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1143 v h) (hints_cons _ _ _ (inp_1139 v h) (by intro d hd; cases hd)))
def cl_17841 : CNF.NClause := [(39,false),(68,false),(8,true),(90,false),(79,true),(76,false),(82,true)]
theorem der_17841 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17841 :=
  CNF.rup_sound cl_17841 [cl_5042,cl_5044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5042 v h) (hints_cons _ _ _ (inp_5044 v h) (by intro d hd; cases hd)))
def cl_17842 : CNF.NClause := [(65,true),(18,false),(3,true),(13,false),(8,true),(23,false)]
theorem der_17842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17842 :=
  CNF.rup_sound cl_17842 [cl_228,cl_15284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_228 v h) (hints_cons _ _ _ (der_15284 v h) (by intro d hd; cases hd)))
def cl_17844 : CNF.NClause := [(63,true),(4,false),(9,true),(14,true),(19,true),(24,false)]
theorem der_17844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17844 :=
  CNF.rup_sound cl_17844 [cl_111,cl_79] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_111 v h) (hints_cons _ _ _ (inp_79 v h) (by intro d hd; cases hd)))
def cl_17850 : CNF.NClause := [(69,true),(20,false),(9,true),(11,false),(2,false),(27,true)]
theorem der_17850 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17850 :=
  CNF.rup_sound cl_17850 [cl_483,cl_491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_483 v h) (hints_cons _ _ _ (inp_491 v h) (by intro d hd; cases hd)))
def cl_17857 : CNF.NClause := [(63,true),(4,false),(9,true),(14,false),(19,true),(24,false)]
theorem der_17857 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17857 :=
  CNF.rup_sound cl_17857 [cl_75,cl_107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_75 v h) (hints_cons _ _ _ (inp_107 v h) (by intro d hd; cases hd)))
def cl_17859 : CNF.NClause := [(69,true),(20,true),(9,true),(11,false),(27,true),(2,false)]
theorem der_17859 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17859 :=
  CNF.rup_sound cl_17859 [cl_499,cl_507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_499 v h) (hints_cons _ _ _ (inp_507 v h) (by intro d hd; cases hd)))
def cl_17869 : CNF.NClause := [(63,true),(4,true),(24,false),(14,false),(9,true),(19,true)]
theorem der_17869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17869 :=
  CNF.rup_sound cl_17869 [cl_76,cl_108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_76 v h) (hints_cons _ _ _ (inp_108 v h) (by intro d hd; cases hd)))
def cl_17873 : CNF.NClause := [(58,false),(89,false),(27,true),(69,false),(76,false),(78,false),(85,true)]
theorem der_17873 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17873 :=
  CNF.rup_sound cl_17873 [cl_7458,cl_7460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7458 v h) (hints_cons _ _ _ (inp_7460 v h) (by intro d hd; cases hd)))
def cl_17875 : CNF.NClause := [(61,false),(87,false),(30,true),(77,false),(72,false),(67,false),(82,true)]
theorem der_17875 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17875 :=
  CNF.rup_sound cl_17875 [cl_7842,cl_7844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7842 v h) (hints_cons _ _ _ (inp_7844 v h) (by intro d hd; cases hd)))
def cl_17878 : CNF.NClause := [(86,true),(18,false),(14,false),(1,true),(22,false),(5,true)]
theorem der_17878 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17878 :=
  CNF.rup_sound cl_17878 [cl_15110,cl_1572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15110 v h) (hints_cons _ _ _ (inp_1572 v h) (by intro d hd; cases hd)))
def cl_17881 : CNF.NClause := [(91,true),(18,false),(24,false),(6,false),(12,false),(26,true)]
theorem der_17881 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17881 :=
  CNF.rup_sound cl_17881 [cl_1889,cl_1890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1889 v h) (hints_cons _ _ _ (inp_1890 v h) (by intro d hd; cases hd)))
def cl_17883 : CNF.NClause := [(90,true),(28,false),(8,true),(11,false),(19,true),(22,false)]
theorem der_17883 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17883 :=
  CNF.rup_sound cl_17883 [cl_1803,cl_1804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1803 v h) (hints_cons _ _ _ (inp_1804 v h) (by intro d hd; cases hd)))
def cl_17884 : CNF.NClause := [(89,true),(23,false),(7,true),(27,true),(16,true),(14,false)]
theorem der_17884 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17884 :=
  CNF.rup_sound cl_17884 [cl_1771,cl_1772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1771 v h) (hints_cons _ _ _ (inp_1772 v h) (by intro d hd; cases hd)))
def cl_17885 : CNF.NClause := [(87,true),(2,false),(1,true),(30,true),(3,true),(4,false)]
theorem der_17885 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17885 :=
  CNF.rup_sound cl_17885 [cl_1644,cl_1643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1644 v h) (hints_cons _ _ _ (inp_1643 v h) (by intro d hd; cases hd)))
def cl_17891 : CNF.NClause := [(89,true),(0,false),(14,false),(16,true),(27,true),(7,true)]
theorem der_17891 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17891 :=
  CNF.rup_sound cl_17891 [cl_17884,cl_1787] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17884 v h) (hints_cons _ _ _ (inp_1787 v h) (by intro d hd; cases hd)))
def cl_17894 : CNF.NClause := [(84,true),(24,false),(16,true),(13,false),(5,true),(28,false)]
theorem der_17894 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17894 :=
  CNF.rup_sound cl_17894 [cl_1420,cl_1419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1420 v h) (hints_cons _ _ _ (inp_1419 v h) (by intro d hd; cases hd)))
def cl_17896 : CNF.NClause := [(17,true),(76,false),(1,true),(8,true),(10,true),(27,true)]
theorem der_17896 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17896 :=
  CNF.rup_sound cl_17896 [cl_944,cl_960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_944 v h) (hints_cons _ _ _ (inp_960 v h) (by intro d hd; cases hd)))
def cl_17899 : CNF.NClause := [(88,true),(0,false),(9,true),(13,false),(17,true),(21,true)]
theorem der_17899 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17899 :=
  CNF.rup_sound cl_17899 [cl_1691,cl_1723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1691 v h) (hints_cons _ _ _ (inp_1723 v h) (by intro d hd; cases hd)))
def cl_17910 : CNF.NClause := [(87,true),(0,false),(2,false),(1,true),(3,true),(30,true)]
theorem der_17910 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17910 :=
  CNF.rup_sound cl_17910 [cl_17885,cl_1659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17885 v h) (hints_cons _ _ _ (inp_1659 v h) (by intro d hd; cases hd)))
def cl_17945 : CNF.NClause := [(111,true),(46,false),(38,true),(34,true),(55,true),(42,false)]
theorem der_17945 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17945 :=
  CNF.rup_sound cl_17945 [cl_3156,cl_3188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3156 v h) (hints_cons _ _ _ (inp_3188 v h) (by intro d hd; cases hd)))
def cl_17947 : CNF.NClause := [(80,true),(15,false),(3,true),(11,false),(24,true),(7,true)]
theorem der_17947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17947 :=
  CNF.rup_sound cl_17947 [cl_1172,cl_1204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1172 v h) (hints_cons _ _ _ (inp_1204 v h) (by intro d hd; cases hd)))
def cl_17955 : CNF.NClause := [(78,true),(15,false),(22,false),(6,false),(27,true),(13,false)]
theorem der_17955 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17955 :=
  CNF.rup_sound cl_17955 [cl_1057,cl_1058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1057 v h) (hints_cons _ _ _ (inp_1058 v h) (by intro d hd; cases hd)))
def cl_17957 : CNF.NClause := [(110,true),(39,true),(52,true),(57,true),(46,false),(33,false)]
theorem der_17957 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17957 :=
  CNF.rup_sound cl_17957 [cl_3123,cl_3127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3123 v h) (hints_cons _ _ _ (inp_3127 v h) (by intro d hd; cases hd)))
def cl_17958 : CNF.NClause := [(112,true),(43,true),(46,false),(59,false),(32,true),(54,true)]
theorem der_17958 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17958 :=
  CNF.rup_sound cl_17958 [cl_3222,cl_3224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3222 v h) (hints_cons _ _ _ (inp_3224 v h) (by intro d hd; cases hd)))
def cl_17959 : CNF.NClause := [(123,true),(51,false),(31,false),(41,true),(46,false),(36,true)]
theorem der_17959 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17959 :=
  CNF.rup_sound cl_17959 [cl_3911,cl_3943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3911 v h) (hints_cons _ _ _ (inp_3943 v h) (by intro d hd; cases hd)))
def cl_17960 : CNF.NClause := [(55,false),(91,false),(24,true),(67,false),(84,false),(76,true),(80,false)]
theorem der_17960 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17960 :=
  CNF.rup_sound cl_17960 [cl_7050,cl_7052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7050 v h) (hints_cons _ _ _ (inp_7052 v h) (by intro d hd; cases hd)))
def cl_17961 : CNF.NClause := [(63,true),(25,false),(24,true),(14,false),(9,true),(19,true)]
theorem der_17961 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17961 :=
  CNF.rup_sound cl_17961 [cl_92,cl_91] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_92 v h) (hints_cons _ _ _ (inp_91 v h) (by intro d hd; cases hd)))
def cl_17971 : CNF.NClause := [(67,true),(23,false),(24,true),(22,false),(30,true),(21,true)]
theorem der_17971 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17971 :=
  CNF.rup_sound cl_17971 [cl_371,cl_372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_371 v h) (hints_cons _ _ _ (inp_372 v h) (by intro d hd; cases hd)))
def cl_17973 : CNF.NClause := [(91,true),(0,false),(26,true),(6,false),(12,false),(24,true)]
theorem der_17973 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17973 :=
  CNF.rup_sound cl_17973 [cl_1905,cl_1913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1905 v h) (hints_cons _ _ _ (inp_1913 v h) (by intro d hd; cases hd)))
def cl_17978 : CNF.NClause := [(83,true),(42,false),(11,false),(66,false),(90,false),(80,false),(72,false)]
theorem der_17978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17978 :=
  CNF.rup_sound cl_17978 [cl_5409,cl_5413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5409 v h) (hints_cons _ _ _ (inp_5413 v h) (by intro d hd; cases hd)))
def cl_17991 : CNF.NClause := [(25,true),(63,false),(9,true),(14,true),(19,true),(24,true)]
theorem der_17991 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17991 :=
  CNF.rup_sound cl_17991 [cl_127,cl_128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_127 v h) (hints_cons _ _ _ (inp_128 v h) (by intro d hd; cases hd)))
def cl_17994 : CNF.NClause := [(67,true),(24,true),(425,false),(21,true),(22,false),(9,true),(30,true)]
theorem der_17994 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17994 :=
  CNF.rup_sound cl_17994 [cl_14059,cl_14056,cl_14065,cl_17971,cl_379,cl_14058,cl_14055,cl_9675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14059 v h) (hints_cons _ _ _ (inp_14056 v h) (hints_cons _ _ _ (inp_14065 v h) (hints_cons _ _ _ (der_17971 v h) (hints_cons _ _ _ (inp_379 v h) (hints_cons _ _ _ (inp_14058 v h) (hints_cons _ _ _ (inp_14055 v h) (hints_cons _ _ _ (inp_9675 v h) (by intro d hd; cases hd)))))))))
def cl_17996 : CNF.NClause := [(69,true),(2,false),(9,true),(11,false),(27,true)]
theorem der_17996 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17996 :=
  CNF.rup_sound cl_17996 [cl_17850,cl_17859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17850 v h) (hints_cons _ _ _ (der_17859 v h) (by intro d hd; cases hd)))
def cl_17997 : CNF.NClause := [(23,false),(83,true),(26,true),(11,false),(17,false),(5,true)]
theorem der_17997 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17997 :=
  CNF.rup_sound cl_17997 [cl_1380,cl_1379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1380 v h) (hints_cons _ _ _ (inp_1379 v h) (by intro d hd; cases hd)))
def cl_17998 : CNF.NClause := [(23,true),(83,true),(26,true),(11,false),(17,false),(5,true)]
theorem der_17998 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17998 :=
  CNF.rup_sound cl_17998 [cl_1396,cl_1395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1396 v h) (hints_cons _ _ _ (inp_1395 v h) (by intro d hd; cases hd)))
def cl_17999 : CNF.NClause := [(83,true),(17,false),(26,true),(11,false),(5,true)]
theorem der_17999 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_17999 :=
  CNF.rup_sound cl_17999 [cl_17997,cl_17998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17997 v h) (hints_cons _ _ _ (der_17998 v h) (by intro d hd; cases hd)))
def cl_18000 : CNF.NClause := [(80,true),(361,true),(364,true),(358,true),(24,true),(342,true),(363,true),(353,true),(3,true),(357,true),(360,true),(11,false),(347,false),(346,true),(350,true),(371,true),(7,true)]
theorem der_18000 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18000 :=
  CNF.rup_sound cl_18000 [cl_13979,cl_17947,cl_13990,cl_1180,cl_9362,cl_9384,cl_14004,cl_9417,cl_9322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13979 v h) (hints_cons _ _ _ (der_17947 v h) (hints_cons _ _ _ (inp_13990 v h) (hints_cons _ _ _ (inp_1180 v h) (hints_cons _ _ _ (inp_9362 v h) (hints_cons _ _ _ (inp_9384 v h) (hints_cons _ _ _ (inp_14004 v h) (hints_cons _ _ _ (inp_9417 v h) (hints_cons _ _ _ (inp_9322 v h) (by intro d hd; cases hd))))))))))
def cl_18018 : CNF.NClause := [(69,true),(18,false),(9,true),(11,false),(27,true)]
theorem der_18018 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18018 :=
  CNF.rup_sound cl_18018 [cl_17656,cl_17996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17656 v h) (hints_cons _ _ _ (der_17996 v h) (by intro d hd; cases hd)))
def cl_18020 : CNF.NClause := [(76,true),(17,false),(1,false),(8,true),(10,true),(27,true)]
theorem der_18020 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18020 :=
  CNF.rup_sound cl_18020 [cl_935,cl_951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_935 v h) (hints_cons _ _ _ (inp_951 v h) (by intro d hd; cases hd)))
def cl_18022 : CNF.NClause := [(86,true),(14,false),(18,false),(1,false),(22,false),(5,true)]
theorem der_18022 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18022 :=
  CNF.rup_sound cl_18022 [cl_15110,cl_1571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15110 v h) (hints_cons _ _ _ (inp_1571 v h) (by intro d hd; cases hd)))
def cl_18028 : CNF.NClause := [(65,true),(23,true),(3,true),(13,false),(18,false),(8,true)]
theorem der_18028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18028 :=
  CNF.rup_sound cl_18028 [cl_212,cl_244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_212 v h) (hints_cons _ _ _ (inp_244 v h) (by intro d hd; cases hd)))
def cl_18034 : CNF.NClause := [(14,true),(86,true),(5,true),(1,false),(18,false),(22,false)]
theorem der_18034 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18034 :=
  CNF.rup_sound cl_18034 [cl_1543,cl_1575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1543 v h) (hints_cons _ _ _ (inp_1575 v h) (by intro d hd; cases hd)))
def cl_18035 : CNF.NClause := [(86,true),(18,false),(5,true),(1,false),(22,false)]
theorem der_18035 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18035 :=
  CNF.rup_sound cl_18035 [cl_18022,cl_18034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18022 v h) (hints_cons _ _ _ (der_18034 v h) (by intro d hd; cases hd)))
def cl_18040 : CNF.NClause := [(91,true),(24,true),(18,false),(26,true),(12,false),(6,false)]
theorem der_18040 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18040 :=
  CNF.rup_sound cl_18040 [cl_17973,cl_1906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17973 v h) (hints_cons _ _ _ (inp_1906 v h) (by intro d hd; cases hd)))
def cl_18043 : CNF.NClause := [(92,true),(20,false),(15,false),(10,true),(5,true)]
theorem der_18043 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18043 :=
  CNF.rup_sound cl_18043 [cl_15410,cl_17675,cl_1960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15410 v h) (hints_cons _ _ _ (der_17675 v h) (hints_cons _ _ _ (inp_1960 v h) (by intro d hd; cases hd))))
def cl_18045 : CNF.NClause := [(87,true),(4,true),(2,false),(1,false),(3,true),(30,true)]
theorem der_18045 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18045 :=
  CNF.rup_sound cl_18045 [cl_1657,cl_1658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1657 v h) (hints_cons _ _ _ (inp_1658 v h) (by intro d hd; cases hd)))
def cl_18053 : CNF.NClause := [(71,true),(26,true),(7,true),(13,false),(19,true),(1,false)]
theorem der_18053 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18053 :=
  CNF.rup_sound cl_18053 [cl_619,cl_635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_619 v h) (hints_cons _ _ _ (inp_635 v h) (by intro d hd; cases hd)))
def cl_18055 : CNF.NClause := [(92,true),(0,false),(5,true),(15,false),(10,true)]
theorem der_18055 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18055 :=
  CNF.rup_sound cl_18055 [cl_17717,cl_17675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17717 v h) (hints_cons _ _ _ (der_17675 v h) (by intro d hd; cases hd)))
def cl_18057 : CNF.NClause := [(67,true),(24,false),(23,true),(22,false),(21,true),(30,true)]
theorem der_18057 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18057 :=
  CNF.rup_sound cl_18057 [cl_363,cl_364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_363 v h) (hints_cons _ _ _ (inp_364 v h) (by intro d hd; cases hd)))
def cl_18068 : CNF.NClause := [(117,true),(45,true),(36,true),(32,false),(49,false),(53,true)]
theorem der_18068 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18068 :=
  CNF.rup_sound cl_18068 [cl_3543,cl_3575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3543 v h) (hints_cons _ _ _ (inp_3575 v h) (by intro d hd; cases hd)))
def cl_18076 : CNF.NClause := [(117,true),(36,true),(32,false),(45,false),(49,false),(53,true)]
theorem der_18076 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18076 :=
  CNF.rup_sound cl_18076 [cl_3539,cl_3571] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3539 v h) (hints_cons _ _ _ (inp_3571 v h) (by intro d hd; cases hd)))
def cl_18088 : CNF.NClause := [(87,true),(4,false),(1,false),(2,false),(3,true),(30,true)]
theorem der_18088 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18088 :=
  CNF.rup_sound cl_18088 [cl_1642,cl_1641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1642 v h) (hints_cons _ _ _ (inp_1641 v h) (by intro d hd; cases hd)))
def cl_18089 : CNF.NClause := [(87,true),(2,false),(30,true),(1,false),(3,true)]
theorem der_18089 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18089 :=
  CNF.rup_sound cl_18089 [cl_18045,cl_18088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18045 v h) (hints_cons _ _ _ (der_18088 v h) (by intro d hd; cases hd)))
def cl_18093 : CNF.NClause := [(89,true),(14,true),(45,false),(70,false),(72,false),(79,true),(86,false)]
theorem der_18093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18093 :=
  CNF.rup_sound cl_18093 [cl_5842,cl_5844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5842 v h) (hints_cons _ _ _ (inp_5844 v h) (by intro d hd; cases hd)))
def cl_18101 : CNF.NClause := [(84,true),(2,false),(16,true),(13,false),(28,false),(5,true)]
theorem der_18101 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18101 :=
  CNF.rup_sound cl_18101 [cl_17894,cl_1435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17894 v h) (hints_cons _ _ _ (inp_1435 v h) (by intro d hd; cases hd)))
def cl_18105 : CNF.NClause := [(67,true),(20,false),(23,true),(21,true),(22,false),(30,true)]
theorem der_18105 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18105 :=
  CNF.rup_sound cl_18105 [cl_18057,cl_379] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18057 v h) (hints_cons _ _ _ (inp_379 v h) (by intro d hd; cases hd)))
def cl_18109 : CNF.NClause := [(89,true),(14,false),(45,false),(70,false),(72,false),(79,false),(86,false)]
theorem der_18109 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18109 :=
  CNF.rup_sound cl_18109 [cl_5827,cl_5825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5827 v h) (hints_cons _ _ _ (inp_5825 v h) (by intro d hd; cases hd)))
def cl_18118 : CNF.NClause := [(111,true),(60,false),(42,false),(34,true),(38,true),(46,true)]
theorem der_18118 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18118 :=
  CNF.rup_sound cl_18118 [cl_3148,cl_3164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3148 v h) (hints_cons _ _ _ (inp_3164 v h) (by intro d hd; cases hd)))
def cl_18120 : CNF.NClause := [(63,true),(4,false),(25,false),(14,true),(19,true),(9,true)]
theorem der_18120 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18120 :=
  CNF.rup_sound cl_18120 [cl_17844,cl_95] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17844 v h) (hints_cons _ _ _ (inp_95 v h) (by intro d hd; cases hd)))
def cl_18121 : CNF.NClause := [(107,true),(41,true),(58,true),(39,true),(48,false),(32,false)]
theorem der_18121 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18121 :=
  CNF.rup_sound cl_18121 [cl_2919,cl_2935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2919 v h) (hints_cons _ _ _ (inp_2935 v h) (by intro d hd; cases hd)))
def cl_18125 : CNF.NClause := [(25,true),(92,false),(0,true),(5,true),(10,true),(15,true)]
theorem der_18125 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18125 :=
  CNF.rup_sound cl_18125 [cl_1968,cl_1984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1968 v h) (hints_cons _ _ _ (inp_1984 v h) (by intro d hd; cases hd)))
def cl_18127 : CNF.NClause := [(91,true),(0,true),(18,false),(26,true),(12,false),(6,false)]
theorem der_18127 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18127 :=
  CNF.rup_sound cl_18127 [cl_17881,cl_1906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17881 v h) (hints_cons _ _ _ (inp_1906 v h) (by intro d hd; cases hd)))
def cl_18128 : CNF.NClause := [(118,true),(61,true),(31,true),(33,false),(32,false),(34,true)]
theorem der_18128 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18128 :=
  CNF.rup_sound cl_18128 [cl_3626,cl_3642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3626 v h) (hints_cons _ _ _ (inp_3642 v h) (by intro d hd; cases hd)))
def cl_18130 : CNF.NClause := [(47,false),(89,true),(16,true),(77,false),(75,true),(66,false),(84,false)]
theorem der_18130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18130 :=
  CNF.rup_sound cl_18130 [cl_6090,cl_6094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6090 v h) (hints_cons _ _ _ (inp_6094 v h) (by intro d hd; cases hd)))
def cl_18133 : CNF.NClause := [(24,false),(63,true),(9,true),(14,false),(19,true)]
theorem der_18133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18133 :=
  CNF.rup_sound cl_18133 [cl_17857,cl_17869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17857 v h) (hints_cons _ _ _ (der_17869 v h) (by intro d hd; cases hd)))
def cl_18134 : CNF.NClause := [(63,true),(25,false),(19,true),(14,false),(9,true)]
theorem der_18134 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18134 :=
  CNF.rup_sound cl_18134 [cl_17961,cl_18133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17961 v h) (hints_cons _ _ _ (der_18133 v h) (by intro d hd; cases hd)))
def cl_18136 : CNF.NClause := [(73,true),(18,false),(28,false),(21,true),(10,true),(7,true)]
theorem der_18136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18136 :=
  CNF.rup_sound cl_18136 [cl_17625,cl_728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17625 v h) (hints_cons _ _ _ (inp_728 v h) (by intro d hd; cases hd)))
def cl_18143 : CNF.NClause := [(80,true),(42,false),(11,false),(69,false),(90,false),(72,false),(83,false)]
theorem der_18143 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18143 :=
  CNF.rup_sound cl_18143 [cl_5393,cl_5395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5393 v h) (hints_cons _ _ _ (inp_5395 v h) (by intro d hd; cases hd)))
def cl_18146 : CNF.NClause := [(66,true),(1,false),(16,true),(6,false),(11,false),(21,true)]
theorem der_18146 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18146 :=
  CNF.rup_sound cl_18146 [cl_281,cl_313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_281 v h) (hints_cons _ _ _ (inp_313 v h) (by intro d hd; cases hd)))
def cl_18164 : CNF.NClause := [(88,true),(17,false),(9,true),(13,false),(21,true)]
theorem der_18164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18164 :=
  CNF.rup_sound cl_18164 [cl_17652,cl_17810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17652 v h) (hints_cons _ _ _ (der_17810 v h) (by intro d hd; cases hd)))
def cl_18176 : CNF.NClause := [(67,true),(23,false),(21,true),(22,false),(30,true)]
theorem der_18176 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18176 :=
  CNF.rup_sound cl_18176 [cl_17971,cl_17660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17971 v h) (hints_cons _ _ _ (der_17660 v h) (by intro d hd; cases hd)))
def cl_18182 : CNF.NClause := [(122,true),(57,true),(55,false),(37,true),(43,true),(49,false)]
theorem der_18182 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18182 :=
  CNF.rup_sound cl_18182 [cl_3880,cl_3879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3880 v h) (hints_cons _ _ _ (inp_3879 v h) (by intro d hd; cases hd)))
def cl_18186 : CNF.NClause := [(14,true),(70,false),(86,false),(45,false),(72,false),(79,false),(63,false)]
theorem der_18186 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18186 :=
  CNF.rup_sound cl_18186 [cl_5762,cl_5826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5762 v h) (hints_cons _ _ _ (inp_5826 v h) (by intro d hd; cases hd)))
def cl_18190 : CNF.NClause := [(100,true),(58,true),(40,true),(42,false),(33,false),(49,false)]
theorem der_18190 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18190 :=
  CNF.rup_sound cl_18190 [cl_2467,cl_2483] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2467 v h) (hints_cons _ _ _ (inp_2483 v h) (by intro d hd; cases hd)))
def cl_18193 : CNF.NClause := [(70,true),(20,true),(6,false),(3,true),(17,false),(28,false)]
theorem der_18193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18193 :=
  CNF.rup_sound cl_18193 [cl_534,cl_530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_534 v h) (hints_cons _ _ _ (inp_530 v h) (by intro d hd; cases hd)))
def cl_18194 : CNF.NClause := [(70,true),(17,false),(6,false),(3,true),(28,false)]
theorem der_18194 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18194 :=
  CNF.rup_sound cl_18194 [cl_17829,cl_18193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17829 v h) (hints_cons _ _ _ (der_18193 v h) (by intro d hd; cases hd)))
def cl_18199 : CNF.NClause := [(68,true),(20,true),(384,true),(16,true),(12,false),(8,true)]
theorem der_18199 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18199 :=
  CNF.rup_sound cl_18199 [cl_14025,cl_14021,cl_13743,cl_17664,cl_412,cl_14010,cl_14034,cl_9496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14025 v h) (hints_cons _ _ _ (inp_14021 v h) (hints_cons _ _ _ (inp_13743 v h) (hints_cons _ _ _ (der_17664 v h) (hints_cons _ _ _ (inp_412 v h) (hints_cons _ _ _ (inp_14010 v h) (hints_cons _ _ _ (inp_14034 v h) (hints_cons _ _ _ (inp_9496 v h) (by intro d hd; cases hd)))))))))
def cl_18200 : CNF.NClause := [(118,true),(31,false),(32,false),(33,false),(34,true),(61,true)]
theorem der_18200 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18200 :=
  CNF.rup_sound cl_18200 [cl_3625,cl_3641] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3625 v h) (hints_cons _ _ _ (inp_3641 v h) (by intro d hd; cases hd)))
def cl_18201 : CNF.NClause := [(55,false),(91,false),(63,true),(67,false),(76,false),(80,false),(84,false)]
theorem der_18201 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18201 :=
  CNF.rup_sound cl_18201 [cl_7043,cl_7044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7043 v h) (hints_cons _ _ _ (inp_7044 v h) (by intro d hd; cases hd)))
def cl_18210 : CNF.NClause := [(35,false),(78,false),(68,false),(63,true),(73,false),(87,false),(83,false)]
theorem der_18210 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18210 :=
  CNF.rup_sound cl_18210 [cl_4483,cl_4484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4483 v h) (hints_cons _ _ _ (inp_4484 v h) (by intro d hd; cases hd)))
def cl_18218 : CNF.NClause := [(115,true),(36,true),(47,true),(44,false),(33,false),(59,false)]
theorem der_18218 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18218 :=
  CNF.rup_sound cl_18218 [cl_3403,cl_3419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3403 v h) (hints_cons _ _ _ (inp_3419 v h) (by intro d hd; cases hd)))
def cl_18229 : CNF.NClause := [(115,true),(47,true),(55,true),(59,false),(33,false),(44,false)]
theorem der_18229 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18229 :=
  CNF.rup_sound cl_18229 [cl_18218,cl_3417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18218 v h) (hints_cons _ _ _ (inp_3417 v h) (by intro d hd; cases hd)))
def cl_18231 : CNF.NClause := [(68,true),(384,true),(16,true),(12,false),(8,true)]
theorem der_18231 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18231 :=
  CNF.rup_sound cl_18231 [cl_17664,cl_17791,cl_18199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17664 v h) (hints_cons _ _ _ (der_17791 v h) (hints_cons _ _ _ (der_18199 v h) (by intro d hd; cases hd))))
def cl_18264 : CNF.NClause := [(115,true),(59,false),(33,false),(44,false),(47,true),(55,false)]
theorem der_18264 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18264 :=
  CNF.rup_sound cl_18264 [cl_3401,cl_18218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3401 v h) (hints_cons _ _ _ (der_18218 v h) (by intro d hd; cases hd)))
def cl_18267 : CNF.NClause := [(65,true),(18,false),(3,true),(13,false),(8,true)]
theorem der_18267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18267 :=
  CNF.rup_sound cl_18267 [cl_17842,cl_18028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17842 v h) (hints_cons _ _ _ (der_18028 v h) (by intro d hd; cases hd)))
def cl_18270 : CNF.NClause := [(92,true),(0,true),(25,false),(15,false),(10,true),(5,true)]
theorem der_18270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18270 :=
  CNF.rup_sound cl_18270 [cl_17696,cl_1944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17696 v h) (hints_cons _ _ _ (inp_1944 v h) (by intro d hd; cases hd)))
def cl_18273 : CNF.NClause := [(14,true),(89,false),(27,true),(16,true),(7,true),(23,true)]
theorem der_18273 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18273 :=
  CNF.rup_sound cl_18273 [cl_1792,cl_1791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1792 v h) (hints_cons _ _ _ (inp_1791 v h) (by intro d hd; cases hd)))
def cl_18275 : CNF.NClause := [(54,false),(83,false),(65,false),(23,true),(67,false),(81,false),(74,false)]
theorem der_18275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18275 :=
  CNF.rup_sound cl_18275 [cl_6914,cl_6978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6914 v h) (hints_cons _ _ _ (inp_6978 v h) (by intro d hd; cases hd)))
def cl_18277 : CNF.NClause := [(100,true),(42,true),(58,true),(49,false),(33,false),(40,true)]
theorem der_18277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18277 :=
  CNF.rup_sound cl_18277 [cl_2471,cl_2487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2471 v h) (hints_cons _ _ _ (inp_2487 v h) (by intro d hd; cases hd)))
def cl_18279 : CNF.NClause := [(48,false),(76,false),(17,true),(88,false),(70,false),(77,false),(64,false)]
theorem der_18279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18279 :=
  CNF.rup_sound cl_18279 [cl_6146,cl_6178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6146 v h) (hints_cons _ _ _ (inp_6178 v h) (by intro d hd; cases hd)))
def cl_18281 : CNF.NClause := [(48,false),(76,true),(17,true),(70,false),(64,false),(77,false),(88,false)]
theorem der_18281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18281 :=
  CNF.rup_sound cl_18281 [cl_6154,cl_6186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6154 v h) (hints_cons _ _ _ (inp_6186 v h) (by intro d hd; cases hd)))
def cl_18285 : CNF.NClause := [(67,true),(23,true),(425,false),(21,true),(22,false),(9,true),(30,true)]
theorem der_18285 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18285 :=
  CNF.rup_sound cl_18285 [cl_18057,cl_17994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18057 v h) (hints_cons _ _ _ (der_17994 v h) (by intro d hd; cases hd)))
def cl_18288 : CNF.NClause := [(117,true),(36,true),(32,false),(53,true),(49,false)]
theorem der_18288 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18288 :=
  CNF.rup_sound cl_18288 [cl_18076,cl_18068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18076 v h) (hints_cons _ _ _ (der_18068 v h) (by intro d hd; cases hd)))
def cl_18295 : CNF.NClause := [(14,false),(4,false),(24,true),(63,true),(19,true),(9,true)]
theorem der_18295 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18295 :=
  CNF.rup_sound cl_18295 [cl_18134,cl_123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18134 v h) (hints_cons _ _ _ (inp_123 v h) (by intro d hd; cases hd)))
def cl_18300 : CNF.NClause := [(38,false),(64,false),(82,true),(7,true),(73,false),(80,false),(71,false)]
theorem der_18300 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18300 :=
  CNF.rup_sound cl_18300 [cl_4898,cl_4962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4898 v h) (hints_cons _ _ _ (inp_4962 v h) (by intro d hd; cases hd)))
def cl_18303 : CNF.NClause := [(92,true),(0,false),(5,true),(25,false),(15,true),(10,true)]
theorem der_18303 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18303 :=
  CNF.rup_sound cl_18303 [cl_1951,cl_17687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1951 v h) (hints_cons _ _ _ (der_17687 v h) (by intro d hd; cases hd)))
def cl_18307 : CNF.NClause := [(70,true),(59,false),(28,false),(90,false),(73,false),(81,false),(84,false)]
theorem der_18307 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18307 :=
  CNF.rup_sound cl_18307 [cl_7557,cl_7559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7557 v h) (hints_cons _ _ _ (inp_7559 v h) (by intro d hd; cases hd)))
def cl_18308 : CNF.NClause := [(79,true),(33,false),(2,false),(69,false),(74,false),(87,false),(84,false)]
theorem der_18308 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18308 :=
  CNF.rup_sound cl_18308 [cl_4243,cl_4241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4243 v h) (hints_cons _ _ _ (inp_4241 v h) (by intro d hd; cases hd)))
def cl_18309 : CNF.NClause := [(80,true),(364,true),(358,true),(363,true),(3,true),(357,true),(360,true),(362,true),(351,true),(368,true),(11,false),(346,true),(349,true),(350,true),(371,true),(7,true)]
theorem der_18309 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18309 :=
  CNF.rup_sound cl_18309 [cl_13979,cl_9411,cl_13742,cl_9393,cl_17683,cl_13999,cl_9359,cl_9305,cl_18000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13979 v h) (hints_cons _ _ _ (inp_9411 v h) (hints_cons _ _ _ (inp_13742 v h) (hints_cons _ _ _ (inp_9393 v h) (hints_cons _ _ _ (der_17683 v h) (hints_cons _ _ _ (inp_13999 v h) (hints_cons _ _ _ (inp_9359 v h) (hints_cons _ _ _ (inp_9305 v h) (hints_cons _ _ _ (der_18000 v h) (by intro d hd; cases hd))))))))))
def cl_18310 : CNF.NClause := [(77,true),(47,false),(16,true),(66,false),(75,true),(68,false),(84,false)]
theorem der_18310 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18310 :=
  CNF.rup_sound cl_18310 [cl_6042,cl_6106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6042 v h) (hints_cons _ _ _ (inp_6106 v h) (by intro d hd; cases hd)))
def cl_18311 : CNF.NClause := [(47,false),(84,false),(16,true),(66,false),(75,true),(68,false)]
theorem der_18311 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18311 :=
  CNF.rup_sound cl_18311 [cl_18310,cl_18130,cl_6026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18310 v h) (hints_cons _ _ _ (der_18130 v h) (hints_cons _ _ _ (inp_6026 v h) (by intro d hd; cases hd))))
def cl_18314 : CNF.NClause := [(14,false),(70,true),(6,false),(3,true),(17,true),(28,false)]
theorem der_18314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18314 :=
  CNF.rup_sound cl_18314 [cl_522,cl_538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_522 v h) (hints_cons _ _ _ (inp_538 v h) (by intro d hd; cases hd)))
def cl_18315 : CNF.NClause := [(14,true),(70,true),(6,false),(3,true),(17,true),(28,false)]
theorem der_18315 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18315 :=
  CNF.rup_sound cl_18315 [cl_542,cl_526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_542 v h) (hints_cons _ _ _ (inp_526 v h) (by intro d hd; cases hd)))
def cl_18316 : CNF.NClause := [(70,true),(17,true),(6,false),(3,true),(28,false)]
theorem der_18316 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18316 :=
  CNF.rup_sound cl_18316 [cl_18314,cl_18315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18314 v h) (hints_cons _ _ _ (der_18315 v h) (by intro d hd; cases hd)))
def cl_18317 : CNF.NClause := [(64,true),(17,true),(2,false),(7,true),(12,false),(22,false)]
theorem der_18317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18317 :=
  CNF.rup_sound cl_18317 [cl_139,cl_171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_139 v h) (hints_cons _ _ _ (inp_171 v h) (by intro d hd; cases hd)))
def cl_18321 : CNF.NClause := [(79,true),(14,false),(2,false),(26,true),(21,true),(8,true)]
theorem der_18321 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18321 :=
  CNF.rup_sound cl_18321 [cl_17836,cl_1147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17836 v h) (hints_cons _ _ _ (inp_1147 v h) (by intro d hd; cases hd)))
def cl_18327 : CNF.NClause := [(83,true),(23,false),(26,true),(11,false),(5,true),(17,true)]
theorem der_18327 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18327 :=
  CNF.rup_sound cl_18327 [cl_1388,cl_1387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1388 v h) (hints_cons _ _ _ (inp_1387 v h) (by intro d hd; cases hd)))
def cl_18352 : CNF.NClause := [(80,true),(15,false),(3,true),(11,false),(7,true)]
theorem der_18352 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18352 :=
  CNF.rup_sound cl_18352 [cl_17683,cl_17947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17683 v h) (hints_cons _ _ _ (der_17947 v h) (by intro d hd; cases hd)))
def cl_18359 : CNF.NClause := [(91,true),(18,false),(26,true),(6,false),(12,false)]
theorem der_18359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18359 :=
  CNF.rup_sound cl_18359 [cl_17881,cl_18040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17881 v h) (hints_cons _ _ _ (der_18040 v h) (by intro d hd; cases hd)))
def cl_18361 : CNF.NClause := [(123,true),(46,false),(56,false),(41,true),(36,true),(31,false)]
theorem der_18361 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18361 :=
  CNF.rup_sound cl_18361 [cl_3927,cl_17959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3927 v h) (hints_cons _ _ _ (der_17959 v h) (by intro d hd; cases hd)))
def cl_18364 : CNF.NClause := [(104,true),(41,true),(49,false),(52,true),(59,false),(38,true)]
theorem der_18364 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18364 :=
  CNF.rup_sound cl_18364 [cl_2711,cl_2712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2711 v h) (hints_cons _ _ _ (inp_2712 v h) (by intro d hd; cases hd)))
def cl_18366 : CNF.NClause := [(92,true),(25,false),(15,false),(10,true),(5,true)]
theorem der_18366 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18366 :=
  CNF.rup_sound cl_18366 [cl_18055,cl_17696,cl_1944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18055 v h) (hints_cons _ _ _ (der_17696 v h) (hints_cons _ _ _ (inp_1944 v h) (by intro d hd; cases hd))))
def cl_18369 : CNF.NClause := [(114,true),(57,true),(36,true),(42,false),(54,false),(48,true)]
theorem der_18369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18369 :=
  CNF.rup_sound cl_18369 [cl_3371,cl_3372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3371 v h) (hints_cons _ _ _ (inp_3372 v h) (by intro d hd; cases hd)))
def cl_18374 : CNF.NClause := [(56,false),(62,false),(63,true),(65,false),(64,false),(92,false),(66,false)]
theorem der_18374 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18374 :=
  CNF.rup_sound cl_18374 [cl_7173,cl_7174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7173 v h) (hints_cons _ _ _ (inp_7174 v h) (by intro d hd; cases hd)))
def cl_18381 : CNF.NClause := [(111,true),(55,false),(46,true),(42,false),(38,true),(34,true)]
theorem der_18381 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18381 :=
  CNF.rup_sound cl_18381 [cl_18118,cl_3180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18118 v h) (hints_cons _ _ _ (inp_3180 v h) (by intro d hd; cases hd)))
def cl_18382 : CNF.NClause := [(94,true),(55,false),(45,true),(40,true),(50,true),(56,false)]
theorem der_18382 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18382 :=
  CNF.rup_sound cl_18382 [cl_2063,cl_2064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2063 v h) (hints_cons _ _ _ (inp_2064 v h) (by intro d hd; cases hd)))
def cl_18386 : CNF.NClause := [(79,true),(57,false),(26,true),(71,false),(75,true),(91,false),(83,false)]
theorem der_18386 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18386 :=
  CNF.rup_sound cl_18386 [cl_7322,cl_7324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7322 v h) (hints_cons _ _ _ (inp_7324 v h) (by intro d hd; cases hd)))
def cl_18387 : CNF.NClause := [(79,false),(57,false),(26,true),(71,false),(75,true),(83,false),(91,false)]
theorem der_18387 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18387 :=
  CNF.rup_sound cl_18387 [cl_7306,cl_7308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7306 v h) (hints_cons _ _ _ (inp_7308 v h) (by intro d hd; cases hd)))
def cl_18388 : CNF.NClause := [(57,false),(83,false),(26,true),(71,false),(75,true),(91,false)]
theorem der_18388 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18388 :=
  CNF.rup_sound cl_18388 [cl_18386,cl_18387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18386 v h) (hints_cons _ _ _ (der_18387 v h) (by intro d hd; cases hd)))
def cl_18389 : CNF.NClause := [(36,false),(83,false),(82,true),(86,false),(84,false),(5,true),(85,true)]
theorem der_18389 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18389 :=
  CNF.rup_sound cl_18389 [cl_4628,cl_4692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4628 v h) (hints_cons _ _ _ (inp_4692 v h) (by intro d hd; cases hd)))
def cl_18412 : CNF.NClause := [(88,true),(29,false),(17,true),(13,false),(21,true),(9,true)]
theorem der_18412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18412 :=
  CNF.rup_sound cl_18412 [cl_17899,cl_1692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17899 v h) (hints_cons _ _ _ (inp_1692 v h) (by intro d hd; cases hd)))
def cl_18426 : CNF.NClause := [(123,true),(56,false),(36,true),(31,false),(41,true),(46,true)]
theorem der_18426 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18426 :=
  CNF.rup_sound cl_18426 [cl_3919,cl_3935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3919 v h) (hints_cons _ _ _ (inp_3935 v h) (by intro d hd; cases hd)))
def cl_18432 : CNF.NClause := [(86,true),(14,true),(5,true),(1,false),(18,true),(22,false)]
theorem der_18432 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18432 :=
  CNF.rup_sound cl_18432 [cl_1551,cl_1583] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1551 v h) (hints_cons _ _ _ (inp_1583 v h) (by intro d hd; cases hd)))
def cl_18433 : CNF.NClause := [(67,true),(425,false),(21,true),(22,false),(9,true),(30,true)]
theorem der_18433 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18433 :=
  CNF.rup_sound cl_18433 [cl_18176,cl_18057,cl_17994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18176 v h) (hints_cons _ _ _ (der_18057 v h) (hints_cons _ _ _ (der_17994 v h) (by intro d hd; cases hd))))
def cl_18441 : CNF.NClause := [(62,true),(29,false),(26,true),(28,false),(27,true),(30,true)]
theorem der_18441 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18441 :=
  CNF.rup_sound cl_18441 [cl_17658,cl_40] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17658 v h) (hints_cons _ _ _ (inp_40 v h) (by intro d hd; cases hd)))
def cl_18457 : CNF.NClause := [(31,false),(0,true),(91,false),(89,false),(88,false),(87,false),(90,false)]
theorem der_18457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18457 :=
  CNF.rup_sound cl_18457 [cl_14845,cl_4034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14845 v h) (hints_cons _ _ _ (inp_4034 v h) (by intro d hd; cases hd)))
def cl_18460 : CNF.NClause := [(0,true),(91,true),(6,false),(12,false),(26,true),(18,true)]
theorem der_18460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18460 :=
  CNF.rup_sound cl_18460 [cl_1898,cl_1914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1898 v h) (hints_cons _ _ _ (inp_1914 v h) (by intro d hd; cases hd)))
def cl_18461 : CNF.NClause := [(0,false),(91,true),(26,true),(6,false),(12,false),(18,true)]
theorem der_18461 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18461 :=
  CNF.rup_sound cl_18461 [cl_1897,cl_17973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1897 v h) (hints_cons _ _ _ (der_17973 v h) (by intro d hd; cases hd)))
def cl_18462 : CNF.NClause := [(91,true),(18,true),(6,false),(12,false),(26,true)]
theorem der_18462 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18462 :=
  CNF.rup_sound cl_18462 [cl_18460,cl_18461] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18460 v h) (hints_cons _ _ _ (der_18461 v h) (by intro d hd; cases hd)))
def cl_18468 : CNF.NClause := [(62,true),(369,false),(26,true),(28,false),(27,true),(7,true),(30,true)]
theorem der_18468 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18468 :=
  CNF.rup_sound cl_18468 [cl_14001,cl_14002,cl_14005,cl_17658,cl_18441,cl_14000,cl_14004,cl_9272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14001 v h) (hints_cons _ _ _ (inp_14002 v h) (hints_cons _ _ _ (inp_14005 v h) (hints_cons _ _ _ (der_17658 v h) (hints_cons _ _ _ (der_18441 v h) (hints_cons _ _ _ (inp_14000 v h) (hints_cons _ _ _ (inp_14004 v h) (hints_cons _ _ _ (inp_9272 v h) (by intro d hd; cases hd)))))))))
def cl_18470 : CNF.NClause := [(100,true),(58,true),(42,false),(40,true),(49,true),(33,false)]
theorem der_18470 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18470 :=
  CNF.rup_sound cl_18470 [cl_2475,cl_2491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2475 v h) (hints_cons _ _ _ (inp_2491 v h) (by intro d hd; cases hd)))
def cl_18474 : CNF.NClause := [(74,true),(2,false),(19,true),(10,true),(6,false)]
theorem der_18474 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18474 :=
  CNF.rup_sound cl_18474 [cl_17802,cl_17777] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17802 v h) (hints_cons _ _ _ (der_17777 v h) (by intro d hd; cases hd)))
def cl_18475 : CNF.NClause := [(86,true),(14,false),(5,true),(1,false),(18,true),(22,false)]
theorem der_18475 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18475 :=
  CNF.rup_sound cl_18475 [cl_1547,cl_1579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1547 v h) (hints_cons _ _ _ (inp_1579 v h) (by intro d hd; cases hd)))
def cl_18476 : CNF.NClause := [(118,true),(34,true),(61,true),(33,false),(32,false)]
theorem der_18476 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18476 :=
  CNF.rup_sound cl_18476 [cl_18128,cl_18200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18128 v h) (hints_cons _ _ _ (der_18200 v h) (by intro d hd; cases hd)))
def cl_18479 : CNF.NClause := [(102,true),(38,true),(44,false),(57,true),(50,true),(32,false)]
theorem der_18479 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18479 :=
  CNF.rup_sound cl_18479 [cl_2603,cl_2619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2603 v h) (hints_cons _ _ _ (inp_2619 v h) (by intro d hd; cases hd)))
def cl_18498 : CNF.NClause := [(40,false),(88,false),(9,true),(75,true),(69,false),(81,false),(82,true)]
theorem der_18498 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18498 :=
  CNF.rup_sound cl_18498 [cl_5162,cl_5164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5162 v h) (hints_cons _ _ _ (inp_5164 v h) (by intro d hd; cases hd)))
def cl_18501 : CNF.NClause := [(54,false),(89,false),(74,false),(65,true),(83,false),(81,false),(67,false)]
theorem der_18501 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18501 :=
  CNF.rup_sound cl_18501 [cl_6915,cl_6916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6915 v h) (hints_cons _ _ _ (inp_6916 v h) (by intro d hd; cases hd)))
def cl_18502 : CNF.NClause := [(115,true),(59,false),(36,true),(33,false),(47,true),(44,true)]
theorem der_18502 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18502 :=
  CNF.rup_sound cl_18502 [cl_3407,cl_3423] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3407 v h) (hints_cons _ _ _ (inp_3423 v h) (by intro d hd; cases hd)))
def cl_18506 : CNF.NClause := [(23,false),(65,true),(3,true),(13,false),(8,true),(18,true)]
theorem der_18506 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18506 :=
  CNF.rup_sound cl_18506 [cl_204,cl_236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_204 v h) (hints_cons _ _ _ (inp_236 v h) (by intro d hd; cases hd)))
def cl_18514 : CNF.NClause := [(86,true),(18,true),(5,true),(1,false),(22,false)]
theorem der_18514 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18514 :=
  CNF.rup_sound cl_18514 [cl_18432,cl_18475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18432 v h) (hints_cons _ _ _ (der_18475 v h) (by intro d hd; cases hd)))
def cl_18546 : CNF.NClause := [(63,true),(24,false),(25,false),(14,true),(19,true),(9,true)]
theorem der_18546 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18546 :=
  CNF.rup_sound cl_18546 [cl_18120,cl_80] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18120 v h) (hints_cons _ _ _ (inp_80 v h) (by intro d hd; cases hd)))
def cl_18548 : CNF.NClause := [(54,false),(89,true),(67,false),(65,false),(74,false),(81,false),(83,false)]
theorem der_18548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18548 :=
  CNF.rup_sound cl_18548 [cl_6977,cl_18275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6977 v h) (hints_cons _ _ _ (der_18275 v h) (by intro d hd; cases hd)))
def cl_18554 : CNF.NClause := [(35,false),(118,true),(61,true),(32,false),(34,true),(33,true)]
theorem der_18554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18554 :=
  CNF.rup_sound cl_18554 [cl_3630,cl_3629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3630 v h) (hints_cons _ _ _ (inp_3629 v h) (by intro d hd; cases hd)))
def cl_18555 : CNF.NClause := [(63,true),(4,false),(14,false),(19,true),(9,true)]
theorem der_18555 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18555 :=
  CNF.rup_sound cl_18555 [cl_18133,cl_18295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18133 v h) (hints_cons _ _ _ (der_18295 v h) (by intro d hd; cases hd)))
def cl_18560 : CNF.NClause := [(4,false),(87,true),(1,false),(2,true),(3,true),(30,true)]
theorem der_18560 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18560 :=
  CNF.rup_sound cl_18560 [cl_1645,cl_1646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1645 v h) (hints_cons _ _ _ (inp_1646 v h) (by intro d hd; cases hd)))
def cl_18564 : CNF.NClause := [(84,true),(2,true),(16,true),(13,false),(28,false),(5,true)]
theorem der_18564 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18564 :=
  CNF.rup_sound cl_18564 [cl_17894,cl_1436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17894 v h) (hints_cons _ _ _ (inp_1436 v h) (by intro d hd; cases hd)))
def cl_18578 : CNF.NClause := [(70,true),(3,true),(6,false),(28,false)]
theorem der_18578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18578 :=
  CNF.rup_sound cl_18578 [cl_18194,cl_18316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18194 v h) (hints_cons _ _ _ (der_18316 v h) (by intro d hd; cases hd)))
def cl_18580 : CNF.NClause := [(98,true),(52,true),(51,false),(61,true),(53,true),(54,false)]
theorem der_18580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18580 :=
  CNF.rup_sound cl_18580 [cl_2343,cl_2359] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2343 v h) (hints_cons _ _ _ (inp_2359 v h) (by intro d hd; cases hd)))
def cl_18584 : CNF.NClause := [(73,false),(35,true),(83,false),(63,false),(87,false),(18,true),(68,false),(78,false),(28,false),(21,true),(10,true),(7,true)]
theorem der_18584 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18584 :=
  CNF.rup_sound cl_18584 [cl_736,cl_4481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_736 v h) (hints_cons _ _ _ (inp_4481 v h) (by intro d hd; cases hd)))
def cl_18587 : CNF.NClause := [(89,true),(355,true),(14,false),(16,true),(27,true),(7,true)]
theorem der_18587 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18587 :=
  CNF.rup_sound cl_18587 [cl_13991,cl_14002,cl_13742,cl_17884,cl_17891,cl_13998,cl_13976,cl_9436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13991 v h) (hints_cons _ _ _ (inp_14002 v h) (hints_cons _ _ _ (inp_13742 v h) (hints_cons _ _ _ (der_17884 v h) (hints_cons _ _ _ (der_17891 v h) (hints_cons _ _ _ (inp_13998 v h) (hints_cons _ _ _ (inp_13976 v h) (hints_cons _ _ _ (inp_9436 v h) (by intro d hd; cases hd)))))))))
def cl_18590 : CNF.NClause := [(74,true),(2,true),(19,true),(10,true),(285,false),(5,true),(6,false)]
theorem der_18590 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18590 :=
  CNF.rup_sound cl_18590 [cl_13918,cl_13934,cl_13925,cl_17666,cl_798,cl_13938,cl_13944,cl_8974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13918 v h) (hints_cons _ _ _ (inp_13934 v h) (hints_cons _ _ _ (inp_13925 v h) (hints_cons _ _ _ (der_17666 v h) (hints_cons _ _ _ (inp_798 v h) (hints_cons _ _ _ (inp_13938 v h) (hints_cons _ _ _ (inp_13944 v h) (hints_cons _ _ _ (inp_8974 v h) (by intro d hd; cases hd)))))))))
def cl_18604 : CNF.NClause := [(64,true),(17,false),(2,true),(22,false),(12,false),(7,true)]
theorem der_18604 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18604 :=
  CNF.rup_sound cl_18604 [cl_15175,cl_164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15175 v h) (hints_cons _ _ _ (inp_164 v h) (by intro d hd; cases hd)))
def cl_18610 : CNF.NClause := [(119,true),(48,true),(44,false),(52,true),(40,true),(31,false)]
theorem der_18610 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18610 :=
  CNF.rup_sound cl_18610 [cl_3675,cl_3707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3675 v h) (hints_cons _ _ _ (inp_3707 v h) (by intro d hd; cases hd)))
end P500
end Percolation.Replay
