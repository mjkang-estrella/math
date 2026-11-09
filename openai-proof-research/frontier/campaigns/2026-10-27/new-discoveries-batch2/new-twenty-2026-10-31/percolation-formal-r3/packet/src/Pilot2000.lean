import Inputs047
namespace Percolation.Replay
namespace P2000
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
def cl_18613 : CNF.NClause := [(83,true),(17,true),(5,true),(11,false),(4,false),(26,true)]
theorem der_18613 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18613 :=
  CNF.rup_sound cl_18613 [cl_1403,cl_18327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1403 v h) (hints_cons _ _ _ (der_18327 v h) (by intro d hd; cases hd)))
def cl_18620 : CNF.NClause := [(17,true),(64,true),(2,true),(12,false),(7,true),(22,false)]
theorem der_18620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18620 :=
  CNF.rup_sound cl_18620 [cl_172,cl_140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_172 v h) (hints_cons _ _ _ (inp_140 v h) (by intro d hd; cases hd)))
def cl_18621 : CNF.NClause := [(64,true),(2,true),(7,true),(22,false),(12,false)]
theorem der_18621 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18621 :=
  CNF.rup_sound cl_18621 [cl_18604,cl_18620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18604 v h) (hints_cons _ _ _ (der_18620 v h) (by intro d hd; cases hd)))
def cl_18629 : CNF.NClause := [(96,true),(56,true),(39,true),(44,false),(49,false),(34,true)]
theorem der_18629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18629 :=
  CNF.rup_sound cl_18629 [cl_2212,cl_2228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2212 v h) (hints_cons _ _ _ (inp_2228 v h) (by intro d hd; cases hd)))
def cl_18636 : CNF.NClause := [(31,false),(92,false),(87,false),(88,false),(91,false),(0,true),(90,false)]
theorem der_18636 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18636 :=
  CNF.rup_sound cl_18636 [cl_3978,cl_18457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3978 v h) (hints_cons _ _ _ (der_18457 v h) (by intro d hd; cases hd)))
def cl_18645 : CNF.NClause := [(96,true),(56,false),(49,false),(39,true),(34,true),(44,false)]
theorem der_18645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18645 :=
  CNF.rup_sound cl_18645 [cl_2180,cl_2196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2180 v h) (hints_cons _ _ _ (inp_2196 v h) (by intro d hd; cases hd)))
def cl_18646 : CNF.NClause := [(100,true),(33,true),(40,true),(49,false),(58,true),(42,false)]
theorem der_18646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18646 :=
  CNF.rup_sound cl_18646 [cl_2468,cl_2484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2468 v h) (hints_cons _ _ _ (inp_2484 v h) (by intro d hd; cases hd)))
def cl_18656 : CNF.NClause := [(36,false),(92,false),(86,false),(84,false),(85,true),(5,true),(82,true)]
theorem der_18656 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18656 :=
  CNF.rup_sound cl_18656 [cl_18389,cl_4632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18389 v h) (hints_cons _ _ _ (inp_4632 v h) (by intro d hd; cases hd)))
def cl_18657 : CNF.NClause := [(57,false),(79,false),(26,true),(71,false),(75,true),(91,false),(62,false)]
theorem der_18657 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18657 :=
  CNF.rup_sound cl_18657 [cl_7338,cl_18388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7338 v h) (hints_cons _ _ _ (der_18388 v h) (by intro d hd; cases hd)))
def cl_18660 : CNF.NClause := [(83,true),(1065,false),(17,true),(26,true),(11,false),(5,true),(30,true)]
theorem der_18660 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18660 :=
  CNF.rup_sound cl_18660 [cl_14683,cl_14692,cl_14671,cl_18613,cl_18327,cl_14670,cl_14689,cl_13677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14683 v h) (hints_cons _ _ _ (inp_14692 v h) (hints_cons _ _ _ (inp_14671 v h) (hints_cons _ _ _ (der_18613 v h) (hints_cons _ _ _ (der_18327 v h) (hints_cons _ _ _ (inp_14670 v h) (hints_cons _ _ _ (inp_14689 v h) (hints_cons _ _ _ (inp_13677 v h) (by intro d hd; cases hd)))))))))
def cl_18661 : CNF.NClause := [(58,false),(76,true),(27,true),(69,false),(78,false),(62,false),(85,true)]
theorem der_18661 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18661 :=
  CNF.rup_sound cl_18661 [cl_7466,cl_7530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7466 v h) (hints_cons _ _ _ (inp_7530 v h) (by intro d hd; cases hd)))
def cl_18664 : CNF.NClause := [(121,true),(42,false),(59,false),(53,true),(39,true),(50,true)]
theorem der_18664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18664 :=
  CNF.rup_sound cl_18664 [cl_3803,cl_3804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3803 v h) (hints_cons _ _ _ (inp_3804 v h) (by intro d hd; cases hd)))
def cl_18669 : CNF.NClause := [(92,true),(15,true),(25,false),(211,false),(2,true),(10,true),(5,true)]
theorem der_18669 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18669 :=
  CNF.rup_sound cl_18669 [cl_13840,cl_13835,cl_13830,cl_18303,cl_13826,cl_1936,cl_8520,cl_13845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13840 v h) (hints_cons _ _ _ (inp_13835 v h) (hints_cons _ _ _ (inp_13830 v h) (hints_cons _ _ _ (der_18303 v h) (hints_cons _ _ _ (inp_13826 v h) (hints_cons _ _ _ (inp_1936 v h) (hints_cons _ _ _ (inp_8520 v h) (hints_cons _ _ _ (inp_13845 v h) (by intro d hd; cases hd)))))))))
def cl_18675 : CNF.NClause := [(111,true),(55,false),(46,false),(34,true),(42,false),(38,true)]
theorem der_18675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18675 :=
  CNF.rup_sound cl_18675 [cl_3140,cl_3172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3140 v h) (hints_cons _ _ _ (inp_3172 v h) (by intro d hd; cases hd)))
def cl_18676 : CNF.NClause := [(111,true),(46,false),(34,true),(42,false),(38,true)]
theorem der_18676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18676 :=
  CNF.rup_sound cl_18676 [cl_17945,cl_18675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17945 v h) (hints_cons _ _ _ (der_18675 v h) (by intro d hd; cases hd)))
def cl_18678 : CNF.NClause := [(60,false),(117,true),(32,true),(49,false),(36,true),(53,true)]
theorem der_18678 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18678 :=
  CNF.rup_sound cl_18678 [cl_3544,cl_3540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3544 v h) (hints_cons _ _ _ (inp_3540 v h) (by intro d hd; cases hd)))
def cl_18681 : CNF.NClause := [(96,true),(39,true),(44,false),(49,false),(34,true)]
theorem der_18681 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18681 :=
  CNF.rup_sound cl_18681 [cl_18645,cl_18629] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18645 v h) (hints_cons _ _ _ (der_18629 v h) (by intro d hd; cases hd)))
def cl_18691 : CNF.NClause := [(77,true),(17,false),(18,false),(16,true),(19,true),(30,true)]
theorem der_18691 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18691 :=
  CNF.rup_sound cl_18691 [cl_17790,cl_1012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17790 v h) (hints_cons _ _ _ (inp_1012 v h) (by intro d hd; cases hd)))
def cl_18695 : CNF.NClause := [(87,true),(352,true),(359,true),(2,true),(1,false),(363,true),(3,true),(360,true),(362,true),(351,true),(349,true),(7,true),(30,true)]
theorem der_18695 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18695 :=
  CNF.rup_sound cl_18695 [cl_13742,cl_18560,cl_13980,cl_1661,cl_9340,cl_13976,cl_9438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13742 v h) (hints_cons _ _ _ (der_18560 v h) (hints_cons _ _ _ (inp_13980 v h) (hints_cons _ _ _ (inp_1661 v h) (hints_cons _ _ _ (inp_9340 v h) (hints_cons _ _ _ (inp_13976 v h) (hints_cons _ _ _ (inp_9438 v h) (by intro d hd; cases hd))))))))
def cl_18697 : CNF.NClause := [(114,true),(48,false),(42,true),(57,true),(35,false),(36,true)]
theorem der_18697 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18697 :=
  CNF.rup_sound cl_18697 [cl_3367,cl_3383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3367 v h) (hints_cons _ _ _ (inp_3383 v h) (by intro d hd; cases hd)))
def cl_18700 : CNF.NClause := [(49,false),(65,false),(18,true),(69,true),(91,false),(73,false),(86,false)]
theorem der_18700 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18700 :=
  CNF.rup_sound cl_18700 [cl_6278,cl_6294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6278 v h) (hints_cons _ _ _ (inp_6294 v h) (by intro d hd; cases hd)))
def cl_18702 : CNF.NClause := [(62,true),(361,true),(359,true),(353,true),(26,true),(357,true),(28,false),(362,true),(351,true),(27,true),(349,true),(7,true),(30,true)]
theorem der_18702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18702 :=
  CNF.rup_sound cl_18702 [cl_13742,cl_18441,cl_18468,cl_14004,cl_9340,cl_9311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13742 v h) (hints_cons _ _ _ (der_18441 v h) (hints_cons _ _ _ (der_18468 v h) (hints_cons _ _ _ (inp_14004 v h) (hints_cons _ _ _ (inp_9340 v h) (hints_cons _ _ _ (inp_9311 v h) (by intro d hd; cases hd)))))))
def cl_18708 : CNF.NClause := [(16,false),(26,true),(9,true),(75,true),(22,false),(10,true)]
theorem der_18708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18708 :=
  CNF.rup_sound cl_18708 [cl_872,cl_871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_872 v h) (hints_cons _ _ _ (inp_871 v h) (by intro d hd; cases hd)))
def cl_18709 : CNF.NClause := [(16,false),(22,false),(75,true),(9,true)]
theorem der_18709 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18709 :=
  CNF.rup_sound cl_18709 [cl_17644,cl_15425,cl_18708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17644 v h) (hints_cons _ _ _ (der_15425 v h) (hints_cons _ _ _ (der_18708 v h) (by intro d hd; cases hd))))
def cl_18714 : CNF.NClause := [(49,false),(73,false),(65,false),(18,true),(69,false),(86,false),(91,false)]
theorem der_18714 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18714 :=
  CNF.rup_sound cl_18714 [cl_6274,cl_6290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6274 v h) (hints_cons _ _ _ (inp_6290 v h) (by intro d hd; cases hd)))
def cl_18716 : CNF.NClause := [(88,true),(17,false),(9,true),(13,true),(0,false),(21,true)]
theorem der_18716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18716 :=
  CNF.rup_sound cl_18716 [cl_1687,cl_1719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1687 v h) (hints_cons _ _ _ (inp_1719 v h) (by intro d hd; cases hd)))
def cl_18723 : CNF.NClause := [(25,true),(65,false),(3,true),(8,true),(13,true),(18,true)]
theorem der_18723 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18723 :=
  CNF.rup_sound cl_18723 [cl_256,cl_240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_256 v h) (hints_cons _ _ _ (inp_240 v h) (by intro d hd; cases hd)))
def cl_18732 : CNF.NClause := [(63,true),(4,false),(25,false),(19,true),(9,true)]
theorem der_18732 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18732 :=
  CNF.rup_sound cl_18732 [cl_18134,cl_18120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18134 v h) (hints_cons _ _ _ (der_18120 v h) (by intro d hd; cases hd)))
def cl_18751 : CNF.NClause := [(84,true),(2,false),(5,true),(13,true),(16,true),(28,false)]
theorem der_18751 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18751 :=
  CNF.rup_sound cl_18751 [cl_1423,cl_1439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1423 v h) (hints_cons _ _ _ (inp_1439 v h) (by intro d hd; cases hd)))
def cl_18755 : CNF.NClause := [(64,true),(2,false),(22,false),(7,true),(12,false)]
theorem der_18755 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18755 :=
  CNF.rup_sound cl_18755 [cl_18317,cl_17831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18317 v h) (hints_cons _ _ _ (der_17831 v h) (by intro d hd; cases hd)))
def cl_18757 : CNF.NClause := [(117,true),(45,false),(49,true),(32,false),(36,true),(53,true)]
theorem der_18757 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18757 :=
  CNF.rup_sound cl_18757 [cl_3547,cl_3579] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3547 v h) (hints_cons _ _ _ (inp_3579 v h) (by intro d hd; cases hd)))
def cl_18759 : CNF.NClause := [(88,true),(17,false),(234,false),(13,true),(21,true),(3,true),(9,true)]
theorem der_18759 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18759 :=
  CNF.rup_sound cl_18759 [cl_13868,cl_13876,cl_13864,cl_18716,cl_13856,cl_1688,cl_8684,cl_13884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13868 v h) (hints_cons _ _ _ (inp_13876 v h) (hints_cons _ _ _ (inp_13864 v h) (hints_cons _ _ _ (der_18716 v h) (hints_cons _ _ _ (inp_13856 v h) (hints_cons _ _ _ (inp_1688 v h) (hints_cons _ _ _ (inp_8684 v h) (hints_cons _ _ _ (inp_13884 v h) (by intro d hd; cases hd)))))))))
def cl_18764 : CNF.NClause := [(83,true),(23,false),(26,true),(11,false),(5,true)]
theorem der_18764 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18764 :=
  CNF.rup_sound cl_18764 [cl_17999,cl_18327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17999 v h) (hints_cons _ _ _ (der_18327 v h) (by intro d hd; cases hd)))
def cl_18766 : CNF.NClause := [(66,true),(21,true),(16,true),(11,false),(6,false)]
theorem der_18766 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18766 :=
  CNF.rup_sound cl_18766 [cl_17635,cl_18146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17635 v h) (hints_cons _ _ _ (der_18146 v h) (by intro d hd; cases hd)))
def cl_18767 : CNF.NClause := [(15,false),(78,true),(27,true),(6,false),(13,true),(22,false)]
theorem der_18767 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18767 :=
  CNF.rup_sound cl_18767 [cl_1061,cl_1062] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1061 v h) (hints_cons _ _ _ (inp_1062 v h) (by intro d hd; cases hd)))
def cl_18774 : CNF.NClause := [(88,true),(29,false),(17,false),(13,true),(21,true),(9,true)]
theorem der_18774 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18774 :=
  CNF.rup_sound cl_18774 [cl_18716,cl_1688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18716 v h) (hints_cons _ _ _ (inp_1688 v h) (by intro d hd; cases hd)))
def cl_18776 : CNF.NClause := [(97,true),(32,false),(52,true),(42,false),(37,true),(47,true)]
theorem der_18776 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18776 :=
  CNF.rup_sound cl_18776 [cl_2267,cl_2299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2267 v h) (hints_cons _ _ _ (inp_2299 v h) (by intro d hd; cases hd)))
def cl_18779 : CNF.NClause := [(87,true),(1,false),(4,false),(3,true),(30,true)]
theorem der_18779 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18779 :=
  CNF.rup_sound cl_18779 [cl_18089,cl_18560] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18089 v h) (hints_cons _ _ _ (der_18560 v h) (by intro d hd; cases hd)))
def cl_18782 : CNF.NClause := [(84,true),(24,false),(13,true),(28,false),(16,true),(5,true)]
theorem der_18782 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18782 :=
  CNF.rup_sound cl_18782 [cl_18751,cl_1424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18751 v h) (hints_cons _ _ _ (inp_1424 v h) (by intro d hd; cases hd)))
def cl_18786 : CNF.NClause := [(64,true),(22,false),(12,false),(7,true)]
theorem der_18786 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18786 :=
  CNF.rup_sound cl_18786 [cl_18755,cl_18621] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18755 v h) (hints_cons _ _ _ (der_18621 v h) (by intro d hd; cases hd)))
def cl_18787 : CNF.NClause := [(54,false),(74,false),(23,false),(83,false),(65,true),(81,false),(67,false)]
theorem der_18787 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18787 :=
  CNF.rup_sound cl_18787 [cl_6979,cl_18501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6979 v h) (hints_cons _ _ _ (der_18501 v h) (by intro d hd; cases hd)))
def cl_18789 : CNF.NClause := [(74,true),(23,false),(19,true),(10,true),(6,false)]
theorem der_18789 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18789 :=
  CNF.rup_sound cl_18789 [cl_18474,cl_17666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18474 v h) (hints_cons _ _ _ (der_17666 v h) (by intro d hd; cases hd)))
def cl_18798 : CNF.NClause := [(54,false),(74,false),(23,true),(83,false),(65,true),(81,false),(67,false)]
theorem der_18798 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18798 :=
  CNF.rup_sound cl_18798 [cl_6980,cl_18501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6980 v h) (hints_cons _ _ _ (der_18501 v h) (by intro d hd; cases hd)))
def cl_18800 : CNF.NClause := [(74,true),(19,true),(10,true),(285,false),(5,true),(6,false)]
theorem der_18800 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18800 :=
  CNF.rup_sound cl_18800 [cl_18474,cl_18590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18474 v h) (hints_cons _ _ _ (der_18590 v h) (by intro d hd; cases hd)))
def cl_18806 : CNF.NClause := [(23,false),(65,true),(3,true),(8,true),(13,true),(18,false)]
theorem der_18806 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18806 :=
  CNF.rup_sound cl_18806 [cl_232,cl_200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_232 v h) (hints_cons _ _ _ (inp_200 v h) (by intro d hd; cases hd)))
def cl_18826 : CNF.NClause := [(63,true),(4,true),(25,false),(736,true),(726,true),(716,true),(739,true),(729,true),(723,true),(734,true),(740,true),(721,true),(720,true),(718,true),(743,true),(19,true),(9,true)]
theorem der_18826 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18826 :=
  CNF.rup_sound cl_18826 [cl_14345,cl_11626,cl_11581,cl_14340,cl_11600,cl_13754,cl_11642,cl_18134,cl_14350,cl_80,cl_11565,cl_11669,cl_11609,cl_14359,cl_11631,cl_11656,cl_11588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14345 v h) (hints_cons _ _ _ (inp_11626 v h) (hints_cons _ _ _ (inp_11581 v h) (hints_cons _ _ _ (inp_14340 v h) (hints_cons _ _ _ (inp_11600 v h) (hints_cons _ _ _ (inp_13754 v h) (hints_cons _ _ _ (inp_11642 v h) (hints_cons _ _ _ (der_18134 v h) (hints_cons _ _ _ (inp_14350 v h) (hints_cons _ _ _ (inp_80 v h) (hints_cons _ _ _ (inp_11565 v h) (hints_cons _ _ _ (inp_11669 v h) (hints_cons _ _ _ (inp_11609 v h) (hints_cons _ _ _ (inp_14359 v h) (hints_cons _ _ _ (inp_11631 v h) (hints_cons _ _ _ (inp_11656 v h) (hints_cons _ _ _ (inp_11588 v h) (by intro d hd; cases hd))))))))))))))))))
def cl_18830 : CNF.NClause := [(1055,true),(1071,true),(1077,true),(1067,true),(1073,true),(1075,true),(1076,true),(1080,true),(1064,true),(1081,true),(1061,true),(1062,true),(1084,false)]
theorem der_18830 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18830 :=
  CNF.rup_sound cl_18830 [cl_13603,cl_13633,cl_13578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13603 v h) (hints_cons _ _ _ (inp_13633 v h) (hints_cons _ _ _ (inp_13578 v h) (by intro d hd; cases hd))))
def cl_18861 : CNF.NClause := [(123,true),(46,false),(41,true),(36,true),(51,true),(56,false)]
theorem der_18861 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18861 :=
  CNF.rup_sound cl_18861 [cl_18361,cl_3928] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18361 v h) (hints_cons _ _ _ (inp_3928 v h) (by intro d hd; cases hd)))
def cl_18862 : CNF.NClause := [(109,true),(46,false),(35,false),(53,true),(37,true),(58,true)]
theorem der_18862 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18862 :=
  CNF.rup_sound cl_18862 [cl_3059,cl_3063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3059 v h) (hints_cons _ _ _ (inp_3063 v h) (by intro d hd; cases hd)))
def cl_18863 : CNF.NClause := [(52,false),(79,false),(21,true),(67,false),(73,false),(85,true),(66,false)]
theorem der_18863 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18863 :=
  CNF.rup_sound cl_18863 [cl_6690,cl_6754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6690 v h) (hints_cons _ _ _ (inp_6754 v h) (by intro d hd; cases hd)))
def cl_18864 : CNF.NClause := [(108,true),(61,true),(47,true),(50,true),(49,false),(46,false)]
theorem der_18864 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18864 :=
  CNF.rup_sound cl_18864 [cl_2995,cl_2999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2995 v h) (hints_cons _ _ _ (inp_2999 v h) (by intro d hd; cases hd)))
def cl_18865 : CNF.NClause := [(112,true),(54,false),(32,true),(46,false),(59,false),(43,true)]
theorem der_18865 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18865 :=
  CNF.rup_sound cl_18865 [cl_3206,cl_3208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3206 v h) (hints_cons _ _ _ (inp_3208 v h) (by intro d hd; cases hd)))
def cl_18878 : CNF.NClause := [(92,true),(15,true),(25,false),(20,false),(10,true),(5,true)]
theorem der_18878 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18878 :=
  CNF.rup_sound cl_18878 [cl_18303,cl_1936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18303 v h) (hints_cons _ _ _ (inp_1936 v h) (by intro d hd; cases hd)))
def cl_18879 : CNF.NClause := [(100,true),(58,true),(49,false),(42,false),(40,true)]
theorem der_18879 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18879 :=
  CNF.rup_sound cl_18879 [cl_18190,cl_18646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18190 v h) (hints_cons _ _ _ (der_18646 v h) (by intro d hd; cases hd)))
def cl_18880 : CNF.NClause := [(117,true),(36,true),(60,false),(49,false),(53,true)]
theorem der_18880 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18880 :=
  CNF.rup_sound cl_18880 [cl_18288,cl_18678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18288 v h) (hints_cons _ _ _ (der_18678 v h) (by intro d hd; cases hd)))
def cl_18884 : CNF.NClause := [(14,true),(79,false),(8,true),(26,true),(15,true),(21,true)]
theorem der_18884 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18884 :=
  CNF.rup_sound cl_18884 [cl_1151,cl_1152] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1151 v h) (hints_cons _ _ _ (inp_1152 v h) (by intro d hd; cases hd)))
def cl_18887 : CNF.NClause := [(96,true),(44,true),(56,false),(39,true),(49,false),(54,false)]
theorem der_18887 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18887 :=
  CNF.rup_sound cl_18887 [cl_2183,cl_2184] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2183 v h) (hints_cons _ _ _ (inp_2184 v h) (by intro d hd; cases hd)))
def cl_18893 : CNF.NClause := [(79,true),(15,false),(976,false),(21,true),(26,true),(27,true),(8,true)]
theorem der_18893 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18893 :=
  CNF.rup_sound cl_18893 [cl_14597,cl_14602,cl_14584,cl_17836,cl_14578,cl_1140,cl_13094,cl_14590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14597 v h) (hints_cons _ _ _ (inp_14602 v h) (hints_cons _ _ _ (inp_14584 v h) (hints_cons _ _ _ (der_17836 v h) (hints_cons _ _ _ (inp_14578 v h) (hints_cons _ _ _ (inp_1140 v h) (hints_cons _ _ _ (inp_13094 v h) (hints_cons _ _ _ (inp_14590 v h) (by intro d hd; cases hd)))))))))
def cl_18895 : CNF.NClause := [(63,true),(24,false),(25,false),(19,true),(9,true)]
theorem der_18895 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18895 :=
  CNF.rup_sound cl_18895 [cl_18134,cl_18546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18134 v h) (hints_cons _ _ _ (der_18546 v h) (by intro d hd; cases hd)))
def cl_18898 : CNF.NClause := [(56,false),(92,false),(62,false),(25,true),(65,false),(66,false),(64,false)]
theorem der_18898 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18898 :=
  CNF.rup_sound cl_18898 [cl_18374,cl_7170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18374 v h) (hints_cons _ _ _ (inp_7170 v h) (by intro d hd; cases hd)))
def cl_18900 : CNF.NClause := [(96,true),(39,true),(56,true),(44,true),(49,false),(54,false)]
theorem der_18900 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18900 :=
  CNF.rup_sound cl_18900 [cl_2215,cl_2216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2215 v h) (hints_cons _ _ _ (inp_2216 v h) (by intro d hd; cases hd)))
def cl_18905 : CNF.NClause := [(63,true),(14,false),(355,false),(366,true),(19,true),(7,true),(9,true)]
theorem der_18905 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18905 :=
  CNF.rup_sound cl_18905 [cl_13994,cl_13984,cl_18555,cl_18133,cl_13980,cl_13999,cl_9279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13994 v h) (hints_cons _ _ _ (inp_13984 v h) (hints_cons _ _ _ (der_18555 v h) (hints_cons _ _ _ (der_18133 v h) (hints_cons _ _ _ (inp_13980 v h) (hints_cons _ _ _ (inp_13999 v h) (hints_cons _ _ _ (inp_9279 v h) (by intro d hd; cases hd))))))))
def cl_18929 : CNF.NClause := [(80,true),(29,false),(3,true),(11,false),(7,true)]
theorem der_18929 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18929 :=
  CNF.rup_sound cl_18929 [cl_17683,cl_18352,cl_1180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17683 v h) (hints_cons _ _ _ (der_18352 v h) (hints_cons _ _ _ (inp_1180 v h) (by intro d hd; cases hd))))
def cl_18940 : CNF.NClause := [(79,true),(15,false),(14,false),(21,true),(26,true),(8,true)]
theorem der_18940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18940 :=
  CNF.rup_sound cl_18940 [cl_17836,cl_1140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17836 v h) (hints_cons _ _ _ (inp_1140 v h) (by intro d hd; cases hd)))
def cl_18946 : CNF.NClause := [(117,true),(36,true),(45,false),(60,true),(49,false),(53,true)]
theorem der_18946 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18946 :=
  CNF.rup_sound cl_18946 [cl_18288,cl_3572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18288 v h) (hints_cons _ _ _ (inp_3572 v h) (by intro d hd; cases hd)))
def cl_18947 : CNF.NClause := [(44,false),(84,false),(13,true),(65,false),(72,false),(88,true),(78,false)]
theorem der_18947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18947 :=
  CNF.rup_sound cl_18947 [cl_5698,cl_5702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5698 v h) (hints_cons _ _ _ (inp_5702 v h) (by intro d hd; cases hd)))
def cl_18948 : CNF.NClause := [(108,true),(47,true),(46,false),(61,true),(49,false),(48,true)]
theorem der_18948 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18948 :=
  CNF.rup_sound cl_18948 [cl_2983,cl_18864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2983 v h) (hints_cons _ _ _ (der_18864 v h) (by intro d hd; cases hd)))
def cl_18949 : CNF.NClause := [(38,false),(80,false),(89,false),(73,false),(64,false),(7,true),(82,true)]
theorem der_18949 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18949 :=
  CNF.rup_sound cl_18949 [cl_18300,cl_4902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18300 v h) (hints_cons _ _ _ (inp_4902 v h) (by intro d hd; cases hd)))
def cl_18962 : CNF.NClause := [(63,true),(24,false),(4,false),(19,true),(9,true)]
theorem der_18962 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18962 :=
  CNF.rup_sound cl_18962 [cl_18555,cl_17844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18555 v h) (hints_cons _ _ _ (der_17844 v h) (by intro d hd; cases hd)))
def cl_18975 : CNF.NClause := [(94,true),(50,true),(45,false),(35,false),(55,true),(40,true)]
theorem der_18975 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18975 :=
  CNF.rup_sound cl_18975 [cl_2075,cl_2107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2075 v h) (hints_cons _ _ _ (inp_2107 v h) (by intro d hd; cases hd)))
def cl_18985 : CNF.NClause := [(108,true),(47,true),(61,true),(46,false),(48,false),(49,false)]
theorem der_18985 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18985 :=
  CNF.rup_sound cl_18985 [cl_2979,cl_18864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2979 v h) (hints_cons _ _ _ (der_18864 v h) (by intro d hd; cases hd)))
def cl_18987 : CNF.NClause := [(117,true),(45,false),(36,true),(49,false),(53,true)]
theorem der_18987 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_18987 :=
  CNF.rup_sound cl_18987 [cl_18880,cl_18946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18880 v h) (hints_cons _ _ _ (der_18946 v h) (by intro d hd; cases hd)))
def cl_19002 : CNF.NClause := [(38,false),(80,false),(89,true),(73,false),(64,false),(7,true),(82,true)]
theorem der_19002 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19002 :=
  CNF.rup_sound cl_19002 [cl_18300,cl_4966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18300 v h) (hints_cons _ _ _ (inp_4966 v h) (by intro d hd; cases hd)))
def cl_19061 : CNF.NClause := [(0,true),(88,false),(9,true),(21,true),(13,true),(17,true)]
theorem der_19061 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19061 :=
  CNF.rup_sound cl_19061 [cl_1696,cl_1728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1696 v h) (hints_cons _ _ _ (inp_1728 v h) (by intro d hd; cases hd)))
def cl_19066 : CNF.NClause := [(1,true),(18,false),(86,true),(5,true),(22,false)]
theorem der_19066 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19066 :=
  CNF.rup_sound cl_19066 [cl_17654,cl_17878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17654 v h) (hints_cons _ _ _ (der_17878 v h) (by intro d hd; cases hd)))
def cl_19067 : CNF.NClause := [(18,false),(86,true),(5,true),(22,false)]
theorem der_19067 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19067 :=
  CNF.rup_sound cl_19067 [cl_18035,cl_19066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18035 v h) (hints_cons _ _ _ (der_19066 v h) (by intro d hd; cases hd)))
def cl_19068 : CNF.NClause := [(978,true),(975,true),(981,true),(979,true),(974,true),(980,true),(982,true),(983,true),(964,true),(977,true),(971,true),(967,true),(991,true),(968,true),(988,false)]
theorem der_19068 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19068 :=
  CNF.rup_sound cl_19068 [cl_13085,cl_13086,cl_13061,cl_13038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13085 v h) (hints_cons _ _ _ (inp_13086 v h) (hints_cons _ _ _ (inp_13061 v h) (hints_cons _ _ _ (inp_13038 v h) (by intro d hd; cases hd)))))
def cl_19069 : CNF.NClause := [(86,true),(239,false),(3,true),(22,false),(5,true)]
theorem der_19069 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19069 :=
  CNF.rup_sound cl_19069 [cl_13860,cl_19067,cl_13873,cl_18514,cl_13857,cl_17775,cl_13869,cl_1552,cl_8671,cl_13884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13860 v h) (hints_cons _ _ _ (der_19067 v h) (hints_cons _ _ _ (inp_13873 v h) (hints_cons _ _ _ (der_18514 v h) (hints_cons _ _ _ (inp_13857 v h) (hints_cons _ _ _ (der_17775 v h) (hints_cons _ _ _ (inp_13869 v h) (hints_cons _ _ _ (inp_1552 v h) (hints_cons _ _ _ (inp_8671 v h) (hints_cons _ _ _ (inp_13884 v h) (by intro d hd; cases hd)))))))))))
def cl_19076 : CNF.NClause := [(90,true),(28,true),(8,true),(11,false),(19,true),(22,false)]
theorem der_19076 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19076 :=
  CNF.rup_sound cl_19076 [cl_1835,cl_1836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1835 v h) (hints_cons _ _ _ (inp_1836 v h) (by intro d hd; cases hd)))
def cl_19079 : CNF.NClause := [(81,true),(15,false),(9,true),(12,false),(1,false),(28,true)]
theorem der_19079 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19079 :=
  CNF.rup_sound cl_19079 [cl_1251,cl_1267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1251 v h) (hints_cons _ _ _ (inp_1267 v h) (by intro d hd; cases hd)))
def cl_19081 : CNF.NClause := [(81,true),(23,false),(1,false),(28,true),(12,false),(9,true)]
theorem der_19081 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19081 :=
  CNF.rup_sound cl_19081 [cl_19079,cl_1259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19079 v h) (hints_cons _ _ _ (inp_1259 v h) (by intro d hd; cases hd)))
def cl_19085 : CNF.NClause := [(70,true),(17,false),(6,false),(3,true),(28,true),(14,true)]
theorem der_19085 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19085 :=
  CNF.rup_sound cl_19085 [cl_550,cl_566] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_550 v h) (hints_cons _ _ _ (inp_566 v h) (by intro d hd; cases hd)))
def cl_19091 : CNF.NClause := [(84,true),(2,false),(5,true),(13,false),(28,true),(16,true)]
theorem der_19091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19091 :=
  CNF.rup_sound cl_19091 [cl_1451,cl_1467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1451 v h) (hints_cons _ _ _ (inp_1467 v h) (by intro d hd; cases hd)))
def cl_19101 : CNF.NClause := [(123,true),(31,true),(51,false),(36,true),(46,false),(41,true)]
theorem der_19101 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19101 :=
  CNF.rup_sound cl_19101 [cl_3912,cl_3944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3912 v h) (hints_cons _ _ _ (inp_3944 v h) (by intro d hd; cases hd)))
def cl_19111 : CNF.NClause := [(78,true),(15,false),(22,false),(6,false),(27,true)]
theorem der_19111 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19111 :=
  CNF.rup_sound cl_19111 [cl_17955,cl_18767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17955 v h) (hints_cons _ _ _ (der_18767 v h) (by intro d hd; cases hd)))
def cl_19114 : CNF.NClause := [(84,true),(13,false),(385,false),(28,true),(16,true),(5,true),(8,true)]
theorem der_19114 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19114 :=
  CNF.rup_sound cl_19114 [cl_14033,cl_14021,cl_14011,cl_19091,cl_14008,cl_1452,cl_9591,cl_14029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14033 v h) (hints_cons _ _ _ (inp_14021 v h) (hints_cons _ _ _ (inp_14011 v h) (hints_cons _ _ _ (der_19091 v h) (hints_cons _ _ _ (inp_14008 v h) (hints_cons _ _ _ (inp_1452 v h) (hints_cons _ _ _ (inp_9591 v h) (hints_cons _ _ _ (inp_14029 v h) (by intro d hd; cases hd)))))))))
def cl_19120 : CNF.NClause := [(92,true),(1017,false),(15,true),(28,true),(10,true),(5,true)]
theorem der_19120 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19120 :=
  CNF.rup_sound cl_19120 [cl_14631,cl_14621,cl_14616,cl_14611,cl_18303,cl_18878,cl_14606,cl_14626,cl_13356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14631 v h) (hints_cons _ _ _ (inp_14621 v h) (hints_cons _ _ _ (inp_14616 v h) (hints_cons _ _ _ (inp_14611 v h) (hints_cons _ _ _ (der_18303 v h) (hints_cons _ _ _ (der_18878 v h) (hints_cons _ _ _ (inp_14606 v h) (hints_cons _ _ _ (inp_14626 v h) (hints_cons _ _ _ (inp_13356 v h) (by intro d hd; cases hd))))))))))
def cl_19126 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false),(28,true)]
theorem der_19126 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19126 :=
  CNF.rup_sound cl_19126 [cl_19079,cl_19081,cl_1275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19079 v h) (hints_cons _ _ _ (der_19081 v h) (hints_cons _ _ _ (inp_1275 v h) (by intro d hd; cases hd))))
def cl_19128 : CNF.NClause := [(15,true),(81,true),(1,true),(291,false),(28,true),(12,false),(5,true),(9,true)]
theorem der_19128 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19128 :=
  CNF.rup_sound cl_19128 [cl_13917,cl_13943,cl_13924,cl_13930,cl_1260,cl_9015,cl_13938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13917 v h) (hints_cons _ _ _ (inp_13943 v h) (hints_cons _ _ _ (inp_13924 v h) (hints_cons _ _ _ (inp_13930 v h) (hints_cons _ _ _ (inp_1260 v h) (hints_cons _ _ _ (inp_9015 v h) (hints_cons _ _ _ (inp_13938 v h) (by intro d hd; cases hd))))))))
def cl_19129 : CNF.NClause := [(15,false),(81,true),(9,true),(12,false),(1,true),(28,true)]
theorem der_19129 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19129 :=
  CNF.rup_sound cl_19129 [cl_1252,cl_1268] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1252 v h) (hints_cons _ _ _ (inp_1268 v h) (by intro d hd; cases hd)))
def cl_19130 : CNF.NClause := [(81,true),(1,true),(9,true),(291,false),(28,true),(12,false),(5,true)]
theorem der_19130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19130 :=
  CNF.rup_sound cl_19130 [cl_19128,cl_19129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19128 v h) (hints_cons _ _ _ (der_19129 v h) (by intro d hd; cases hd)))
def cl_19133 : CNF.NClause := [(69,true),(20,false),(18,true),(27,true),(11,false),(9,true)]
theorem der_19133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19133 :=
  CNF.rup_sound cl_19133 [cl_17996,cl_492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17996 v h) (hints_cons _ _ _ (inp_492 v h) (by intro d hd; cases hd)))
def cl_19134 : CNF.NClause := [(94,true),(55,false),(45,false),(40,true),(50,true),(56,false)]
theorem der_19134 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19134 :=
  CNF.rup_sound cl_19134 [cl_2060,cl_2059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2060 v h) (hints_cons _ _ _ (inp_2059 v h) (by intro d hd; cases hd)))
def cl_19135 : CNF.NClause := [(95,true),(38,true),(56,false),(53,true),(43,true),(48,false)]
theorem der_19135 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19135 :=
  CNF.rup_sound cl_19135 [cl_2135,cl_2136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2135 v h) (hints_cons _ _ _ (inp_2136 v h) (by intro d hd; cases hd)))
def cl_19136 : CNF.NClause := [(34,false),(65,false),(3,true),(80,false),(75,true),(70,false),(85,true)]
theorem der_19136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19136 :=
  CNF.rup_sound cl_19136 [cl_4458,cl_4394] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4458 v h) (hints_cons _ _ _ (inp_4394 v h) (by intro d hd; cases hd)))
def cl_19137 : CNF.NClause := [(32,false),(71,false),(66,false),(86,false),(76,false),(81,false),(1,true)]
theorem der_19137 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19137 :=
  CNF.rup_sound cl_19137 [cl_4098,cl_4162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4098 v h) (hints_cons _ _ _ (inp_4162 v h) (by intro d hd; cases hd)))
def cl_19138 : CNF.NClause := [(87,true),(1,true),(4,false),(1058,true),(3,true),(30,true)]
theorem der_19138 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19138 :=
  CNF.rup_sound cl_19138 [cl_14667,cl_14669,cl_13765,cl_17885,cl_14668,cl_1647,cl_13698,cl_14666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14667 v h) (hints_cons _ _ _ (inp_14669 v h) (hints_cons _ _ _ (inp_13765 v h) (hints_cons _ _ _ (der_17885 v h) (hints_cons _ _ _ (inp_14668 v h) (hints_cons _ _ _ (inp_1647 v h) (hints_cons _ _ _ (inp_13698 v h) (hints_cons _ _ _ (inp_14666 v h) (by intro d hd; cases hd)))))))))
def cl_19139 : CNF.NClause := [(281,true),(299,false),(280,true),(283,true),(297,true),(307,true),(298,true),(301,true),(282,true),(306,true),(287,true),(288,true),(309,true)]
theorem der_19139 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19139 :=
  CNF.rup_sound cl_19139 [cl_8941,cl_9053,cl_9069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8941 v h) (hints_cons _ _ _ (inp_9053 v h) (hints_cons _ _ _ (inp_9069 v h) (by intro d hd; cases hd))))
def cl_19149 : CNF.NClause := [(70,true),(17,false),(6,false),(3,true),(14,false),(28,true)]
theorem der_19149 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19149 :=
  CNF.rup_sound cl_19149 [cl_546,cl_562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_546 v h) (hints_cons _ _ _ (inp_562 v h) (by intro d hd; cases hd)))
def cl_19151 : CNF.NClause := [(70,true),(14,false),(6,false),(3,true),(28,true),(17,true)]
theorem der_19151 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19151 :=
  CNF.rup_sound cl_19151 [cl_554,cl_570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_554 v h) (hints_cons _ _ _ (inp_570 v h) (by intro d hd; cases hd)))
def cl_19153 : CNF.NClause := [(112,true),(40,true),(46,true),(43,true),(32,false),(54,false)]
theorem der_19153 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19153 :=
  CNF.rup_sound cl_19153 [cl_3215,cl_3247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3215 v h) (hints_cons _ _ _ (inp_3247 v h) (by intro d hd; cases hd)))
def cl_19154 : CNF.NClause := [(118,true),(34,true),(33,false),(32,false)]
theorem der_19154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19154 :=
  CNF.rup_sound cl_19154 [cl_18476,cl_15536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18476 v h) (hints_cons _ _ _ (der_15536 v h) (by intro d hd; cases hd)))
def cl_19155 : CNF.NClause := [(61,false),(87,false),(30,true),(67,false),(72,false),(77,true),(82,true)]
theorem der_19155 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19155 :=
  CNF.rup_sound cl_19155 [cl_7858,cl_7860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7858 v h) (hints_cons _ _ _ (inp_7860 v h) (by intro d hd; cases hd)))
def cl_19157 : CNF.NClause := [(88,true),(13,false),(385,false),(17,true),(21,true),(9,true),(8,true)]
theorem der_19157 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19157 :=
  CNF.rup_sound cl_19157 [cl_14022,cl_14026,cl_14014,cl_17899,cl_18412,cl_14006,cl_14034,cl_9615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14022 v h) (hints_cons _ _ _ (inp_14026 v h) (hints_cons _ _ _ (inp_14014 v h) (hints_cons _ _ _ (der_17899 v h) (hints_cons _ _ _ (der_18412 v h) (hints_cons _ _ _ (inp_14006 v h) (hints_cons _ _ _ (inp_14034 v h) (hints_cons _ _ _ (inp_9615 v h) (by intro d hd; cases hd)))))))))
def cl_19162 : CNF.NClause := [(94,true),(55,false),(40,true),(50,true),(35,true),(45,false)]
theorem der_19162 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19162 :=
  CNF.rup_sound cl_19162 [cl_19134,cl_2092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19134 v h) (hints_cons _ _ _ (inp_2092 v h) (by intro d hd; cases hd)))
def cl_19166 : CNF.NClause := [(76,false),(55,true),(1,false),(84,false),(80,false),(17,true),(63,false),(91,false),(67,false),(10,true),(27,true),(8,true)]
theorem der_19166 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19166 :=
  CNF.rup_sound cl_19166 [cl_959,cl_7041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_959 v h) (hints_cons _ _ _ (inp_7041 v h) (by intro d hd; cases hd)))
def cl_19168 : CNF.NClause := [(65,true),(292,false),(18,true),(3,true),(5,true),(8,true)]
theorem der_19168 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19168 :=
  CNF.rup_sound cl_19168 [cl_13928,cl_13933,cl_13919,cl_13923,cl_18506,cl_220,cl_13938,cl_13940,cl_8919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13928 v h) (hints_cons _ _ _ (inp_13933 v h) (hints_cons _ _ _ (inp_13919 v h) (hints_cons _ _ _ (inp_13923 v h) (hints_cons _ _ _ (der_18506 v h) (hints_cons _ _ _ (inp_220 v h) (hints_cons _ _ _ (inp_13938 v h) (hints_cons _ _ _ (inp_13940 v h) (hints_cons _ _ _ (inp_8919 v h) (by intro d hd; cases hd))))))))))
def cl_19170 : CNF.NClause := [(71,true),(20,false),(13,false),(19,true),(26,true),(7,true)]
theorem der_19170 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19170 :=
  CNF.rup_sound cl_19170 [cl_18053,cl_620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18053 v h) (hints_cons _ _ _ (inp_620 v h) (by intro d hd; cases hd)))
def cl_19172 : CNF.NClause := [(81,true),(291,false),(28,true),(12,false),(5,true),(9,true)]
theorem der_19172 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19172 :=
  CNF.rup_sound cl_19172 [cl_19126,cl_19130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19126 v h) (hints_cons _ _ _ (der_19130 v h) (by intro d hd; cases hd)))
def cl_19174 : CNF.NClause := [(92,true),(1010,true),(15,true),(1009,true),(1014,true),(1004,true),(998,true),(1018,true),(1008,true),(1013,true),(1019,true),(1000,true),(999,true),(995,true),(28,true),(10,true),(5,true)]
theorem der_19174 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19174 :=
  CNF.rup_sound cl_19174 [cl_14621,cl_13763,cl_14616,cl_13242,cl_13277,cl_19120,cl_13197,cl_13193,cl_13281,cl_13224,cl_13339,cl_14626,cl_14606,cl_17687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14621 v h) (hints_cons _ _ _ (inp_13763 v h) (hints_cons _ _ _ (inp_14616 v h) (hints_cons _ _ _ (inp_13242 v h) (hints_cons _ _ _ (inp_13277 v h) (hints_cons _ _ _ (der_19120 v h) (hints_cons _ _ _ (inp_13197 v h) (hints_cons _ _ _ (inp_13193 v h) (hints_cons _ _ _ (inp_13281 v h) (hints_cons _ _ _ (inp_13224 v h) (hints_cons _ _ _ (inp_13339 v h) (hints_cons _ _ _ (inp_14626 v h) (hints_cons _ _ _ (inp_14606 v h) (hints_cons _ _ _ (der_17687 v h) (by intro d hd; cases hd)))))))))))))))
def cl_19189 : CNF.NClause := [(96,true),(44,true),(39,true),(54,false),(49,false)]
theorem der_19189 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19189 :=
  CNF.rup_sound cl_19189 [cl_18887,cl_18900] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18887 v h) (hints_cons _ _ _ (der_18900 v h) (by intro d hd; cases hd)))
def cl_19193 : CNF.NClause := [(55,false),(122,true),(31,false),(49,false),(37,true),(43,true)]
theorem der_19193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19193 :=
  CNF.rup_sound cl_19193 [cl_18182,cl_3847] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18182 v h) (hints_cons _ _ _ (inp_3847 v h) (by intro d hd; cases hd)))
def cl_19194 : CNF.NClause := [(55,true),(122,true),(31,false),(37,true),(49,false),(43,true)]
theorem der_19194 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19194 :=
  CNF.rup_sound cl_19194 [cl_3895,cl_3863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3895 v h) (hints_cons _ _ _ (inp_3863 v h) (by intro d hd; cases hd)))
def cl_19195 : CNF.NClause := [(122,true),(31,false),(43,true),(49,false),(37,true)]
theorem der_19195 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19195 :=
  CNF.rup_sound cl_19195 [cl_19193,cl_19194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19193 v h) (hints_cons _ _ _ (der_19194 v h) (by intro d hd; cases hd)))
def cl_19200 : CNF.NClause := [(65,true),(373,true),(13,true),(392,true),(18,false),(400,true),(384,true),(393,true),(394,true),(3,true),(398,true),(388,true),(399,true),(378,false),(379,true),(381,true),(402,true),(8,true)]
theorem der_19200 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19200 :=
  CNF.rup_sound cl_19200 [cl_14009,cl_18806,cl_216,cl_14028,cl_14030,cl_9572,cl_9487,cl_9457,cl_9484,cl_9567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14009 v h) (hints_cons _ _ _ (der_18806 v h) (hints_cons _ _ _ (inp_216 v h) (hints_cons _ _ _ (inp_14028 v h) (hints_cons _ _ _ (inp_14030 v h) (hints_cons _ _ _ (inp_9572 v h) (hints_cons _ _ _ (inp_9487 v h) (hints_cons _ _ _ (inp_9457 v h) (hints_cons _ _ _ (inp_9484 v h) (hints_cons _ _ _ (inp_9567 v h) (by intro d hd; cases hd)))))))))))
def cl_19225 : CNF.NClause := [(112,true),(40,true),(32,false),(54,false),(43,true),(46,false)]
theorem der_19225 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19225 :=
  CNF.rup_sound cl_19225 [cl_3207,cl_3239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3207 v h) (hints_cons _ _ _ (inp_3239 v h) (by intro d hd; cases hd)))
def cl_19228 : CNF.NClause := [(2,true),(84,false),(13,true),(5,true),(16,true),(28,true)]
theorem der_19228 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19228 :=
  CNF.rup_sound cl_19228 [cl_1456,cl_1472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1456 v h) (hints_cons _ _ _ (inp_1472 v h) (by intro d hd; cases hd)))
def cl_19233 : CNF.NClause := [(376,true),(389,true),(385,true),(400,true),(391,true),(393,true),(394,true),(388,true),(382,true),(399,true),(378,false),(379,true),(402,true)]
theorem der_19233 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19233 :=
  CNF.rup_sound cl_19233 [cl_9524,cl_9556,cl_9551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_9524 v h) (hints_cons _ _ _ (inp_9556 v h) (hints_cons _ _ _ (inp_9551 v h) (by intro d hd; cases hd))))
def cl_19240 : CNF.NClause := [(123,true),(41,true),(51,false),(36,true),(46,false)]
theorem der_19240 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19240 :=
  CNF.rup_sound cl_19240 [cl_19101,cl_17959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19101 v h) (hints_cons _ _ _ (der_17959 v h) (by intro d hd; cases hd)))
def cl_19241 : CNF.NClause := [(40,false),(63,false),(69,false),(81,false),(75,true),(9,true),(82,true)]
theorem der_19241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19241 :=
  CNF.rup_sound cl_19241 [cl_18498,cl_5226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18498 v h) (hints_cons _ _ _ (inp_5226 v h) (by intro d hd; cases hd)))
def cl_19243 : CNF.NClause := [(20,true),(13,true),(7,true),(71,false),(19,true),(26,true)]
theorem der_19243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19243 :=
  CNF.rup_sound cl_19243 [cl_639,cl_640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_639 v h) (hints_cons _ _ _ (inp_640 v h) (by intro d hd; cases hd)))
def cl_19247 : CNF.NClause := [(101,true),(48,true),(45,false),(51,false),(34,true),(37,true)]
theorem der_19247 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19247 :=
  CNF.rup_sound cl_19247 [cl_2508,cl_2540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2508 v h) (hints_cons _ _ _ (inp_2540 v h) (by intro d hd; cases hd)))
def cl_19250 : CNF.NClause := [(76,true),(1,false),(32,false),(66,false),(71,false),(81,false),(86,false)]
theorem der_19250 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19250 :=
  CNF.rup_sound cl_19250 [cl_4105,cl_4169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4105 v h) (hints_cons _ _ _ (inp_4169 v h) (by intro d hd; cases hd)))
def cl_19253 : CNF.NClause := [(76,true),(1,true),(86,false),(32,false),(71,false),(66,false),(81,false)]
theorem der_19253 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19253 :=
  CNF.rup_sound cl_19253 [cl_4106,cl_4170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4106 v h) (hints_cons _ _ _ (inp_4170 v h) (by intro d hd; cases hd)))
def cl_19254 : CNF.NClause := [(1,true),(32,false),(66,false),(86,false),(71,false),(81,false)]
theorem der_19254 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19254 :=
  CNF.rup_sound cl_19254 [cl_19137,cl_19253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19137 v h) (hints_cons _ _ _ (der_19253 v h) (by intro d hd; cases hd)))
def cl_19255 : CNF.NClause := [(84,true),(24,false),(13,false),(28,true),(16,true),(5,true)]
theorem der_19255 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19255 :=
  CNF.rup_sound cl_19255 [cl_19091,cl_1452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19091 v h) (hints_cons _ _ _ (inp_1452 v h) (by intro d hd; cases hd)))
def cl_19263 : CNF.NClause := [(79,false),(92,true),(77,false),(80,false),(81,false),(78,false),(46,false)]
theorem der_19263 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19263 :=
  CNF.rup_sound cl_19263 [cl_5954,cl_5953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5954 v h) (hints_cons _ _ _ (inp_5953 v h) (by intro d hd; cases hd)))
def cl_19267 : CNF.NClause := [(79,false),(80,true),(46,false),(15,true),(81,false),(77,false),(78,false)]
theorem der_19267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19267 :=
  CNF.rup_sound cl_19267 [cl_5906,cl_5970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5906 v h) (hints_cons _ _ _ (inp_5970 v h) (by intro d hd; cases hd)))
def cl_19269 : CNF.NClause := [(79,true),(15,true),(46,false),(78,false),(80,true),(81,false),(77,false)]
theorem der_19269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19269 :=
  CNF.rup_sound cl_19269 [cl_5914,cl_5978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5914 v h) (hints_cons _ _ _ (inp_5978 v h) (by intro d hd; cases hd)))
def cl_19270 : CNF.NClause := [(80,true),(15,true),(46,false),(78,false),(81,false),(77,false)]
theorem der_19270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19270 :=
  CNF.rup_sound cl_19270 [cl_19267,cl_19269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19267 v h) (hints_cons _ _ _ (der_19269 v h) (by intro d hd; cases hd)))
def cl_19279 : CNF.NClause := [(15,true),(78,false),(46,false),(77,false),(80,false),(81,false),(92,false)]
theorem der_19279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19279 :=
  CNF.rup_sound cl_19279 [cl_5890,cl_5898] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5890 v h) (hints_cons _ _ _ (inp_5898 v h) (by intro d hd; cases hd)))
def cl_19282 : CNF.NClause := [(112,true),(32,false),(40,true),(54,true),(43,true),(46,false)]
theorem der_19282 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19282 :=
  CNF.rup_sound cl_19282 [cl_3223,cl_3255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3223 v h) (hints_cons _ _ _ (inp_3255 v h) (by intro d hd; cases hd)))
def cl_19292 : CNF.NClause := [(58,false),(89,true),(27,true),(69,false),(76,false),(78,false),(85,true)]
theorem der_19292 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19292 :=
  CNF.rup_sound cl_19292 [cl_7522,cl_7524] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7522 v h) (hints_cons _ _ _ (inp_7524 v h) (by intro d hd; cases hd)))
def cl_19297 : CNF.NClause := [(78,true),(22,false),(6,false),(27,true)]
theorem der_19297 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19297 :=
  CNF.rup_sound cl_19297 [cl_17617,cl_19111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17617 v h) (hints_cons _ _ _ (der_19111 v h) (by intro d hd; cases hd)))
def cl_19305 : CNF.NClause := [(0,true),(1,true),(30,true),(87,false),(3,true),(4,true)]
theorem der_19305 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19305 :=
  CNF.rup_sound cl_19305 [cl_1660,cl_1664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1660 v h) (hints_cons _ _ _ (inp_1664 v h) (by intro d hd; cases hd)))
def cl_19307 : CNF.NClause := [(59,false),(84,false),(28,true),(90,false),(73,true),(70,false),(81,false)]
theorem der_19307 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19307 :=
  CNF.rup_sound cl_19307 [cl_7562,cl_7564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7562 v h) (hints_cons _ _ _ (inp_7564 v h) (by intro d hd; cases hd)))
def cl_19314 : CNF.NClause := [(100,true),(33,false),(49,false),(51,false),(42,false),(40,true)]
theorem der_19314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19314 :=
  CNF.rup_sound cl_19314 [cl_18879,cl_2435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18879 v h) (hints_cons _ _ _ (inp_2435 v h) (by intro d hd; cases hd)))
def cl_19315 : CNF.NClause := [(104,true),(41,true),(35,false),(52,true),(49,false),(38,true)]
theorem der_19315 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19315 :=
  CNF.rup_sound cl_19315 [cl_18364,cl_2743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18364 v h) (hints_cons _ _ _ (inp_2743 v h) (by intro d hd; cases hd)))
def cl_19316 : CNF.NClause := [(58,false),(76,true),(89,false),(69,false),(85,true),(78,false),(27,true)]
theorem der_19316 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19316 :=
  CNF.rup_sound cl_19316 [cl_18661,cl_7468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18661 v h) (hints_cons _ _ _ (inp_7468 v h) (by intro d hd; cases hd)))
def cl_19317 : CNF.NClause := [(54,true),(114,true),(36,true),(42,false),(57,true),(35,false)]
theorem der_19317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19317 :=
  CNF.rup_sound cl_19317 [cl_3379,cl_3387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3379 v h) (hints_cons _ _ _ (inp_3387 v h) (by intro d hd; cases hd)))
def cl_19323 : CNF.NClause := [(59,false),(73,false),(28,true),(70,false),(81,false),(90,false),(62,false)]
theorem der_19323 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19323 :=
  CNF.rup_sound cl_19323 [cl_7554,cl_7586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7554 v h) (hints_cons _ _ _ (inp_7586 v h) (by intro d hd; cases hd)))
def cl_19324 : CNF.NClause := [(47,false),(89,false),(16,true),(68,false),(75,true),(66,false),(77,false)]
theorem der_19324 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19324 :=
  CNF.rup_sound cl_19324 [cl_6058,cl_18311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6058 v h) (hints_cons _ _ _ (der_18311 v h) (by intro d hd; cases hd)))
def cl_19328 : CNF.NClause := [(59,false),(84,false),(28,true),(90,false),(81,false),(70,false)]
theorem der_19328 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19328 :=
  CNF.rup_sound cl_19328 [cl_19307,cl_19323,cl_7556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19307 v h) (hints_cons _ _ _ (der_19323 v h) (hints_cons _ _ _ (inp_7556 v h) (by intro d hd; cases hd))))
def cl_19340 : CNF.NClause := [(1078,false),(1,true),(76,true),(10,true),(27,true),(8,true),(30,true)]
theorem der_19340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19340 :=
  CNF.rup_sound cl_19340 [cl_14667,cl_14676,cl_14693,cl_14674,cl_14690,cl_13633,cl_936,cl_14683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14667 v h) (hints_cons _ _ _ (inp_14676 v h) (hints_cons _ _ _ (inp_14693 v h) (hints_cons _ _ _ (inp_14674 v h) (hints_cons _ _ _ (inp_14690 v h) (hints_cons _ _ _ (inp_13633 v h) (hints_cons _ _ _ (inp_936 v h) (hints_cons _ _ _ (inp_14683 v h) (by intro d hd; cases hd)))))))))
def cl_19353 : CNF.NClause := [(92,true),(0,false),(5,true),(20,false),(10,true)]
theorem der_19353 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19353 :=
  CNF.rup_sound cl_19353 [cl_17687,cl_18043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17687 v h) (hints_cons _ _ _ (der_18043 v h) (by intro d hd; cases hd)))
def cl_19367 : CNF.NClause := [(1009,true),(92,true),(15,true),(1014,true),(998,true),(1018,true),(1008,true),(1013,true),(1019,true),(1022,true),(1011,true),(1000,true),(999,true),(995,true),(28,true),(10,true),(5,true)]
theorem der_19367 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19367 :=
  CNF.rup_sound cl_19367 [cl_14621,cl_14611,cl_13317,cl_13268,cl_19174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14621 v h) (hints_cons _ _ _ (inp_14611 v h) (hints_cons _ _ _ (inp_13317 v h) (hints_cons _ _ _ (inp_13268 v h) (hints_cons _ _ _ (der_19174 v h) (by intro d hd; cases hd))))))
def cl_19368 : CNF.NClause := [(1012,false),(1017,true),(92,true),(1007,true),(28,true),(10,true),(5,true)]
theorem der_19368 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19368 :=
  CNF.rup_sound cl_19368 [cl_14616,cl_14611,cl_14626,cl_13357,cl_19353,cl_14606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14616 v h) (hints_cons _ _ _ (inp_14611 v h) (hints_cons _ _ _ (inp_14626 v h) (hints_cons _ _ _ (inp_13357 v h) (hints_cons _ _ _ (der_19353 v h) (hints_cons _ _ _ (inp_14606 v h) (by intro d hd; cases hd)))))))
def cl_19375 : CNF.NClause := [(39,false),(79,false),(82,true),(8,true),(76,false),(68,false),(90,false)]
theorem der_19375 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19375 :=
  CNF.rup_sound cl_19375 [cl_5026,cl_5028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5026 v h) (hints_cons _ _ _ (inp_5028 v h) (by intro d hd; cases hd)))
def cl_19376 : CNF.NClause := [(65,true),(387,true),(18,false),(400,true),(384,true),(391,true),(393,true),(394,true),(3,true),(398,true),(388,true),(399,true),(378,false),(379,true),(381,true),(402,true),(8,true)]
theorem der_19376 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19376 :=
  CNF.rup_sound cl_19376 [cl_18267,cl_18806,cl_14018,cl_14028,cl_9575,cl_9511,cl_19200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18267 v h) (hints_cons _ _ _ (der_18806 v h) (hints_cons _ _ _ (inp_14018 v h) (hints_cons _ _ _ (inp_14028 v h) (hints_cons _ _ _ (inp_9575 v h) (hints_cons _ _ _ (inp_9511 v h) (hints_cons _ _ _ (der_19200 v h) (by intro d hd; cases hd))))))))
def cl_19383 : CNF.NClause := [(17,true),(77,false),(16,true),(30,true),(18,true),(19,true)]
theorem der_19383 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19383 :=
  CNF.rup_sound cl_19383 [cl_1023,cl_1024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1023 v h) (hints_cons _ _ _ (inp_1024 v h) (by intro d hd; cases hd)))
def cl_19398 : CNF.NClause := [(1079,true),(1055,true),(63,true),(1068,true),(1082,true),(19,true),(1075,true),(1076,true),(1080,true),(1064,true),(1081,true),(1059,true),(1061,true),(9,true),(30,true)]
theorem der_19398 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19398 :=
  CNF.rup_sound cl_19398 [cl_14685,cl_14675,cl_13765,cl_13548,cl_13692,cl_13616,cl_14670,cl_13559,cl_18962,cl_14690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14685 v h) (hints_cons _ _ _ (inp_14675 v h) (hints_cons _ _ _ (inp_13765 v h) (hints_cons _ _ _ (inp_13548 v h) (hints_cons _ _ _ (inp_13692 v h) (hints_cons _ _ _ (inp_13616 v h) (hints_cons _ _ _ (inp_14670 v h) (hints_cons _ _ _ (inp_13559 v h) (hints_cons _ _ _ (der_18962 v h) (hints_cons _ _ _ (inp_14690 v h) (by intro d hd; cases hd)))))))))))
def cl_19399 : CNF.NClause := [(1079,false),(63,true),(1068,true),(19,true),(9,true),(30,true)]
theorem der_19399 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19399 :=
  CNF.rup_sound cl_19399 [cl_14685,cl_14675,cl_14691,cl_18732,cl_18895,cl_14670,cl_14690,cl_13554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14685 v h) (hints_cons _ _ _ (inp_14675 v h) (hints_cons _ _ _ (inp_14691 v h) (hints_cons _ _ _ (der_18732 v h) (hints_cons _ _ _ (der_18895 v h) (hints_cons _ _ _ (inp_14670 v h) (hints_cons _ _ _ (inp_14690 v h) (hints_cons _ _ _ (inp_13554 v h) (by intro d hd; cases hd)))))))))
def cl_19400 : CNF.NClause := [(1058,false),(63,true),(1068,true),(19,true),(9,true),(30,true)]
theorem der_19400 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19400 :=
  CNF.rup_sound cl_19400 [cl_19399,cl_14685,cl_14675,cl_14670,cl_13559,cl_18962,cl_14690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19399 v h) (hints_cons _ _ _ (inp_14685 v h) (hints_cons _ _ _ (inp_14675 v h) (hints_cons _ _ _ (inp_14670 v h) (hints_cons _ _ _ (inp_13559 v h) (hints_cons _ _ _ (der_18962 v h) (hints_cons _ _ _ (inp_14690 v h) (by intro d hd; cases hd))))))))
def cl_19405 : CNF.NClause := [(119,true),(31,false),(52,true),(40,true),(48,false)]
theorem der_19405 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19405 :=
  CNF.rup_sound cl_19405 [cl_17647,cl_17649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17647 v h) (hints_cons _ _ _ (der_17649 v h) (by intro d hd; cases hd)))
def cl_19409 : CNF.NClause := [(107,true),(39,true),(32,false),(55,true),(48,false),(41,true)]
theorem der_19409 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19409 :=
  CNF.rup_sound cl_19409 [cl_2903,cl_18121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2903 v h) (hints_cons _ _ _ (der_18121 v h) (by intro d hd; cases hd)))
def cl_19414 : CNF.NClause := [(96,true),(54,false),(49,false),(34,true),(39,true)]
theorem der_19414 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19414 :=
  CNF.rup_sound cl_19414 [cl_19189,cl_18681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19189 v h) (hints_cons _ _ _ (der_18681 v h) (by intro d hd; cases hd)))
def cl_19415 : CNF.NClause := [(88,true),(0,false),(17,false),(21,true),(9,true)]
theorem der_19415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19415 :=
  CNF.rup_sound cl_19415 [cl_18164,cl_18716] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18164 v h) (hints_cons _ _ _ (der_18716 v h) (by intro d hd; cases hd)))
def cl_19422 : CNF.NClause := [(65,true),(23,false),(18,false),(3,true),(8,true)]
theorem der_19422 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19422 :=
  CNF.rup_sound cl_19422 [cl_18267,cl_18806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18267 v h) (hints_cons _ _ _ (der_18806 v h) (by intro d hd; cases hd)))
def cl_19430 : CNF.NClause := [(88,true),(29,false),(17,false),(21,true),(9,true)]
theorem der_19430 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19430 :=
  CNF.rup_sound cl_19430 [cl_18164,cl_18774] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18164 v h) (hints_cons _ _ _ (der_18774 v h) (by intro d hd; cases hd)))
def cl_19437 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(56,false)]
theorem der_19437 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19437 :=
  CNF.rup_sound cl_19437 [cl_18426,cl_18361] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18426 v h) (hints_cons _ _ _ (der_18361 v h) (by intro d hd; cases hd)))
def cl_19450 : CNF.NClause := [(52,false),(73,false),(88,false),(85,true),(66,false),(67,false),(21,true)]
theorem der_19450 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19450 :=
  CNF.rup_sound cl_19450 [cl_18863,cl_6706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18863 v h) (hints_cons _ _ _ (inp_6706 v h) (by intro d hd; cases hd)))
def cl_19452 : CNF.NClause := [(87,true),(4,false),(1,true),(0,false),(3,true),(30,true)]
theorem der_19452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19452 :=
  CNF.rup_sound cl_19452 [cl_17885,cl_1647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17885 v h) (hints_cons _ _ _ (inp_1647 v h) (by intro d hd; cases hd)))
def cl_19460 : CNF.NClause := [(76,true),(24,false),(17,false),(10,true),(27,true),(8,true)]
theorem der_19460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19460 :=
  CNF.rup_sound cl_19460 [cl_18020,cl_936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18020 v h) (hints_cons _ _ _ (inp_936 v h) (by intro d hd; cases hd)))
def cl_19476 : CNF.NClause := [(63,false),(77,true),(90,false),(50,false),(19,true),(74,false),(85,true)]
theorem der_19476 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19476 :=
  CNF.rup_sound cl_19476 [cl_6450,cl_6454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6450 v h) (hints_cons _ _ _ (inp_6454 v h) (by intro d hd; cases hd)))
def cl_19477 : CNF.NClause := [(63,true),(77,true),(19,true),(90,false),(74,false),(50,false),(85,true)]
theorem der_19477 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19477 :=
  CNF.rup_sound cl_19477 [cl_6452,cl_6456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6452 v h) (hints_cons _ _ _ (inp_6456 v h) (by intro d hd; cases hd)))
def cl_19478 : CNF.NClause := [(77,true),(50,false),(90,false),(85,true),(19,true),(74,false)]
theorem der_19478 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19478 :=
  CNF.rup_sound cl_19478 [cl_19476,cl_19477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19476 v h) (hints_cons _ _ _ (der_19477 v h) (by intro d hd; cases hd)))
def cl_19479 : CNF.NClause := [(71,true),(77,false),(74,false),(19,true),(90,false),(50,false),(85,true)]
theorem der_19479 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19479 :=
  CNF.rup_sound cl_19479 [cl_6438,cl_6440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6438 v h) (hints_cons _ _ _ (inp_6440 v h) (by intro d hd; cases hd)))
def cl_19480 : CNF.NClause := [(77,false),(50,false),(90,false),(74,false),(19,true),(85,true)]
theorem der_19480 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19480 :=
  CNF.rup_sound cl_19480 [cl_17832,cl_19479] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17832 v h) (hints_cons _ _ _ (der_19479 v h) (by intro d hd; cases hd)))
def cl_19481 : CNF.NClause := [(50,false),(90,false),(74,false),(85,true),(19,true)]
theorem der_19481 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19481 :=
  CNF.rup_sound cl_19481 [cl_19478,cl_19480] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19478 v h) (hints_cons _ _ _ (der_19480 v h) (by intro d hd; cases hd)))
def cl_19483 : CNF.NClause := [(11,true),(69,true),(42,false),(66,false),(72,false),(90,false),(83,false)]
theorem der_19483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19483 :=
  CNF.rup_sound cl_19483 [cl_5382,cl_5398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5382 v h) (hints_cons _ _ _ (inp_5398 v h) (by intro d hd; cases hd)))
def cl_19485 : CNF.NClause := [(11,true),(69,false),(90,false),(42,false),(83,false),(72,false),(66,false)]
theorem der_19485 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19485 :=
  CNF.rup_sound cl_19485 [cl_5394,cl_15401] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5394 v h) (hints_cons _ _ _ (der_15401 v h) (by intro d hd; cases hd)))
def cl_19487 : CNF.NClause := [(69,false),(11,true),(90,false),(66,false),(42,false),(72,true),(83,false)]
theorem der_19487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19487 :=
  CNF.rup_sound cl_19487 [cl_5386,cl_5402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5386 v h) (hints_cons _ _ _ (inp_5402 v h) (by intro d hd; cases hd)))
def cl_19488 : CNF.NClause := [(69,true),(83,false),(42,false),(66,false),(90,false),(72,true),(11,true)]
theorem der_19488 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19488 :=
  CNF.rup_sound cl_19488 [cl_5390,cl_5406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5390 v h) (hints_cons _ _ _ (inp_5406 v h) (by intro d hd; cases hd)))
def cl_19489 : CNF.NClause := [(11,true),(83,false),(90,false),(66,false),(42,false),(72,true)]
theorem der_19489 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19489 :=
  CNF.rup_sound cl_19489 [cl_19487,cl_19488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19487 v h) (hints_cons _ _ _ (der_19488 v h) (by intro d hd; cases hd)))
def cl_19491 : CNF.NClause := [(69,true),(72,true),(83,true),(66,false),(90,false),(11,true),(42,false)]
theorem der_19491 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19491 :=
  CNF.rup_sound cl_19491 [cl_5422,cl_5438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5422 v h) (hints_cons _ _ _ (inp_5438 v h) (by intro d hd; cases hd)))
def cl_19492 : CNF.NClause := [(69,false),(11,true),(90,false),(66,false),(42,false),(72,true),(83,true)]
theorem der_19492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19492 :=
  CNF.rup_sound cl_19492 [cl_5418,cl_5434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5418 v h) (hints_cons _ _ _ (inp_5434 v h) (by intro d hd; cases hd)))
def cl_19493 : CNF.NClause := [(72,true),(11,true),(83,true),(66,false),(90,false),(42,false)]
theorem der_19493 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19493 :=
  CNF.rup_sound cl_19493 [cl_19491,cl_19492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19491 v h) (hints_cons _ _ _ (der_19492 v h) (by intro d hd; cases hd)))
def cl_19495 : CNF.NClause := [(69,false),(11,true),(90,false),(42,false),(72,false),(83,true),(66,false)]
theorem der_19495 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19495 :=
  CNF.rup_sound cl_19495 [cl_5410,cl_5426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5410 v h) (hints_cons _ _ _ (inp_5426 v h) (by intro d hd; cases hd)))
def cl_19496 : CNF.NClause := [(69,true),(11,true),(90,false),(66,false),(42,false),(72,false),(83,true)]
theorem der_19496 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19496 :=
  CNF.rup_sound cl_19496 [cl_5430,cl_5414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5430 v h) (hints_cons _ _ _ (inp_5414 v h) (by intro d hd; cases hd)))
def cl_19497 : CNF.NClause := [(11,true),(42,false),(90,false),(66,false),(72,false),(83,true)]
theorem der_19497 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19497 :=
  CNF.rup_sound cl_19497 [cl_19495,cl_19496] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19495 v h) (hints_cons _ _ _ (der_19496 v h) (by intro d hd; cases hd)))
def cl_19502 : CNF.NClause := [(1077,false),(17,true),(11,true),(83,true),(26,true),(5,true),(30,true)]
theorem der_19502 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19502 :=
  CNF.rup_sound cl_19502 [cl_14683,cl_14677,cl_14692,cl_14671,cl_14689,cl_13675,cl_1391,cl_14670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14683 v h) (hints_cons _ _ _ (inp_14677 v h) (hints_cons _ _ _ (inp_14692 v h) (hints_cons _ _ _ (inp_14671 v h) (hints_cons _ _ _ (inp_14689 v h) (hints_cons _ _ _ (inp_13675 v h) (hints_cons _ _ _ (inp_1391 v h) (hints_cons _ _ _ (inp_14670 v h) (by intro d hd; cases hd)))))))))
def cl_19506 : CNF.NClause := [(4,false),(17,false),(5,true),(26,true),(83,true),(11,true)]
theorem der_19506 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19506 :=
  CNF.rup_sound cl_19506 [cl_1383,cl_1399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1383 v h) (hints_cons _ _ _ (inp_1399 v h) (by intro d hd; cases hd)))
def cl_19512 : CNF.NClause := [(20,false),(11,true),(9,true),(27,true),(18,false),(69,true)]
theorem der_19512 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19512 :=
  CNF.rup_sound cl_19512 [cl_488,cl_487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_488 v h) (hints_cons _ _ _ (inp_487 v h) (by intro d hd; cases hd)))
def cl_19519 : CNF.NClause := [(13,false),(72,true),(10,true),(12,false),(30,true),(11,true)]
theorem der_19519 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19519 :=
  CNF.rup_sound cl_19519 [cl_676,cl_692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_676 v h) (hints_cons _ _ _ (inp_692 v h) (by intro d hd; cases hd)))
def cl_19521 : CNF.NClause := [(72,true),(19,true),(5,true),(30,true),(27,true),(3,true),(21,true),(10,true)]
theorem der_19521 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19521 :=
  CNF.rup_sound cl_19521 [cl_13936,cl_13740,cl_13942,cl_13919,cl_13934,cl_9040,cl_13927,cl_17632,cl_19519,cl_13746,cl_14106,cl_14101,cl_14099,cl_14116,cl_14122,cl_14125,cl_14114,cl_684,cl_14108,cl_10155,cl_14109,cl_10078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13936 v h) (hints_cons _ _ _ (inp_13740 v h) (hints_cons _ _ _ (inp_13942 v h) (hints_cons _ _ _ (inp_13919 v h) (hints_cons _ _ _ (inp_13934 v h) (hints_cons _ _ _ (inp_9040 v h) (hints_cons _ _ _ (inp_13927 v h) (hints_cons _ _ _ (der_17632 v h) (hints_cons _ _ _ (der_19519 v h) (hints_cons _ _ _ (inp_13746 v h) (hints_cons _ _ _ (inp_14106 v h) (hints_cons _ _ _ (inp_14101 v h) (hints_cons _ _ _ (inp_14099 v h) (hints_cons _ _ _ (inp_14116 v h) (hints_cons _ _ _ (inp_14122 v h) (hints_cons _ _ _ (inp_14125 v h) (hints_cons _ _ _ (inp_14114 v h) (hints_cons _ _ _ (inp_684 v h) (hints_cons _ _ _ (inp_14108 v h) (hints_cons _ _ _ (inp_10155 v h) (hints_cons _ _ _ (inp_14109 v h) (hints_cons _ _ _ (inp_10078 v h) (by intro d hd; cases hd)))))))))))))))))))))))
def cl_19525 : CNF.NClause := [(108,true),(61,true),(47,true),(49,false),(48,false),(50,true)]
theorem der_19525 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19525 :=
  CNF.rup_sound cl_19525 [cl_2996,cl_18864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2996 v h) (hints_cons _ _ _ (der_18864 v h) (by intro d hd; cases hd)))
def cl_19529 : CNF.NClause := [(80,true),(15,false),(3,true),(7,true),(11,true),(24,false)]
theorem der_19529 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19529 :=
  CNF.rup_sound cl_19529 [cl_1192,cl_15488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1192 v h) (hints_cons _ _ _ (der_15488 v h) (by intro d hd; cases hd)))
def cl_19531 : CNF.NClause := [(87,true),(2,false),(4,false),(30,true),(3,true)]
theorem der_19531 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19531 :=
  CNF.rup_sound cl_19531 [cl_18089,cl_17885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18089 v h) (hints_cons _ _ _ (der_17885 v h) (by intro d hd; cases hd)))
def cl_19537 : CNF.NClause := [(87,true),(2,false),(4,true),(0,false),(3,true),(30,true)]
theorem der_19537 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19537 :=
  CNF.rup_sound cl_19537 [cl_1659,cl_18089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1659 v h) (hints_cons _ _ _ (der_18089 v h) (by intro d hd; cases hd)))
def cl_19541 : CNF.NClause := [(17,true),(4,true),(11,true),(26,true),(83,false),(5,true)]
theorem der_19541 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19541 :=
  CNF.rup_sound cl_19541 [cl_1392,cl_1408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1392 v h) (hints_cons _ _ _ (inp_1408 v h) (by intro d hd; cases hd)))
def cl_19545 : CNF.NClause := [(89,true),(713,false),(0,false),(19,true),(27,true),(7,true),(16,true)]
theorem der_19545 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19545 :=
  CNF.rup_sound cl_19545 [cl_14362,cl_14343,cl_14352,cl_17891,cl_14350,cl_1775,cl_11669,cl_14358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14362 v h) (hints_cons _ _ _ (inp_14343 v h) (hints_cons _ _ _ (inp_14352 v h) (hints_cons _ _ _ (der_17891 v h) (hints_cons _ _ _ (inp_14350 v h) (hints_cons _ _ _ (inp_1775 v h) (hints_cons _ _ _ (inp_11669 v h) (hints_cons _ _ _ (inp_14358 v h) (by intro d hd; cases hd)))))))))
def cl_19548 : CNF.NClause := [(34,false),(80,false),(87,false),(65,false),(85,true),(3,true),(75,true)]
theorem der_19548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19548 :=
  CNF.rup_sound cl_19548 [cl_19136,cl_4398] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19136 v h) (hints_cons _ _ _ (inp_4398 v h) (by intro d hd; cases hd)))
def cl_19557 : CNF.NClause := [(87,true),(4,false),(0,false),(30,true),(3,true)]
theorem der_19557 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19557 :=
  CNF.rup_sound cl_19557 [cl_18779,cl_19452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18779 v h) (hints_cons _ _ _ (der_19452 v h) (by intro d hd; cases hd)))
def cl_19562 : CNF.NClause := [(2,true),(33,false),(87,false),(79,false),(74,false),(64,false),(69,false)]
theorem der_19562 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19562 :=
  CNF.rup_sound cl_19562 [cl_4226,cl_4258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4226 v h) (hints_cons _ _ _ (inp_4258 v h) (by intro d hd; cases hd)))
def cl_19564 : CNF.NClause := [(104,true),(59,true),(41,true),(52,true),(35,false),(49,false)]
theorem der_19564 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19564 :=
  CNF.rup_sound cl_19564 [cl_2743,cl_2741] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2743 v h) (hints_cons _ _ _ (inp_2741 v h) (by intro d hd; cases hd)))
def cl_19570 : CNF.NClause := [(48,false),(70,false),(77,false),(88,false),(83,false),(64,false),(76,true)]
theorem der_19570 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19570 :=
  CNF.rup_sound cl_19570 [cl_6153,cl_18281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6153 v h) (hints_cons _ _ _ (der_18281 v h) (by intro d hd; cases hd)))
def cl_19573 : CNF.NClause := [(70,true),(14,false),(6,false),(3,true),(28,true)]
theorem der_19573 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19573 :=
  CNF.rup_sound cl_19573 [cl_19149,cl_19151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19149 v h) (hints_cons _ _ _ (der_19151 v h) (by intro d hd; cases hd)))
def cl_19580 : CNF.NClause := [(77,true),(15,false),(18,false),(19,true),(30,true),(16,true)]
theorem der_19580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19580 :=
  CNF.rup_sound cl_19580 [cl_18691,cl_1015] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18691 v h) (hints_cons _ _ _ (inp_1015 v h) (by intro d hd; cases hd)))
def cl_19584 : CNF.NClause := [(34,false),(87,false),(70,false),(65,false),(85,true),(3,true),(75,true)]
theorem der_19584 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19584 :=
  CNF.rup_sound cl_19584 [cl_19136,cl_4410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19136 v h) (hints_cons _ _ _ (inp_4410 v h) (by intro d hd; cases hd)))
def cl_19588 : CNF.NClause := [(69,true),(49,false),(18,false),(65,false),(91,false),(77,false),(86,false)]
theorem der_19588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19588 :=
  CNF.rup_sound cl_19588 [cl_6277,cl_6285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6277 v h) (hints_cons _ _ _ (inp_6285 v h) (by intro d hd; cases hd)))
def cl_19589 : CNF.NClause := [(34,false),(80,true),(3,true),(85,true),(75,true),(70,false),(65,false)]
theorem der_19589 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19589 :=
  CNF.rup_sound cl_19589 [cl_4474,cl_19584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4474 v h) (hints_cons _ _ _ (der_19584 v h) (by intro d hd; cases hd)))
def cl_19590 : CNF.NClause := [(34,false),(70,false),(3,true),(85,true),(75,true),(65,false)]
theorem der_19590 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19590 :=
  CNF.rup_sound cl_19590 [cl_19136,cl_19589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19136 v h) (hints_cons _ _ _ (der_19589 v h) (by intro d hd; cases hd)))
def cl_19598 : CNF.NClause := [(90,true),(19,true),(456,false),(8,true),(22,false),(28,true),(10,true)]
theorem der_19598 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19598 :=
  CNF.rup_sound cl_19598 [cl_14084,cl_14074,cl_14093,cl_19076,cl_1839,cl_14076,cl_14066,cl_9997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14084 v h) (hints_cons _ _ _ (inp_14074 v h) (hints_cons _ _ _ (inp_14093 v h) (hints_cons _ _ _ (der_19076 v h) (hints_cons _ _ _ (inp_1839 v h) (hints_cons _ _ _ (inp_14076 v h) (hints_cons _ _ _ (inp_14066 v h) (hints_cons _ _ _ (inp_9997 v h) (by intro d hd; cases hd)))))))))
def cl_19601 : CNF.NClause := [(65,true),(13,false),(25,false),(18,true),(8,true),(3,true)]
theorem der_19601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19601 :=
  CNF.rup_sound cl_19601 [cl_18506,cl_220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18506 v h) (hints_cons _ _ _ (inp_220 v h) (by intro d hd; cases hd)))
def cl_19605 : CNF.NClause := [(111,true),(38,true),(42,true),(46,false),(34,true),(55,false)]
theorem der_19605 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19605 :=
  CNF.rup_sound cl_19605 [cl_3144,cl_3176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3144 v h) (hints_cons _ _ _ (inp_3176 v h) (by intro d hd; cases hd)))
def cl_19607 : CNF.NClause := [(2,true),(69,false),(9,true),(27,true),(11,true),(18,true)]
theorem der_19607 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19607 :=
  CNF.rup_sound cl_19607 [cl_496,cl_512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_496 v h) (hints_cons _ _ _ (inp_512 v h) (by intro d hd; cases hd)))
def cl_19609 : CNF.NClause := [(84,true),(2,false),(24,false),(5,true),(28,true),(16,true)]
theorem der_19609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19609 :=
  CNF.rup_sound cl_19609 [cl_19091,cl_1455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19091 v h) (hints_cons _ _ _ (inp_1455 v h) (by intro d hd; cases hd)))
def cl_19612 : CNF.NClause := [(80,true),(458,false),(11,true),(7,true),(3,true),(10,true)]
theorem der_19612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19612 :=
  CNF.rup_sound cl_19612 [cl_14089,cl_14076,cl_14073,cl_14069,cl_19529,cl_1168,cl_14080,cl_14094,cl_9937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14089 v h) (hints_cons _ _ _ (inp_14076 v h) (hints_cons _ _ _ (inp_14073 v h) (hints_cons _ _ _ (inp_14069 v h) (hints_cons _ _ _ (der_19529 v h) (hints_cons _ _ _ (inp_1168 v h) (hints_cons _ _ _ (inp_14080 v h) (hints_cons _ _ _ (inp_14094 v h) (hints_cons _ _ _ (inp_9937 v h) (by intro d hd; cases hd))))))))))
def cl_19620 : CNF.NClause := [(1,false),(66,true),(16,true),(11,true),(6,false),(21,true)]
theorem der_19620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19620 :=
  CNF.rup_sound cl_19620 [cl_317,cl_285] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_317 v h) (hints_cons _ _ _ (inp_285 v h) (by intro d hd; cases hd)))
def cl_19621 : CNF.NClause := [(66,true),(781,true),(6,false),(16,true),(21,true)]
theorem der_19621 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19621 :=
  CNF.rup_sound cl_19621 [cl_14412,cl_13756,cl_18766,cl_14407,cl_19620,cl_14397,cl_286,cl_11899,cl_14420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14412 v h) (hints_cons _ _ _ (inp_13756 v h) (hints_cons _ _ _ (der_18766 v h) (hints_cons _ _ _ (inp_14407 v h) (hints_cons _ _ _ (der_19620 v h) (hints_cons _ _ _ (inp_14397 v h) (hints_cons _ _ _ (inp_286 v h) (hints_cons _ _ _ (inp_11899 v h) (hints_cons _ _ _ (inp_14420 v h) (by intro d hd; cases hd))))))))))
def cl_19622 : CNF.NClause := [(63,true),(14,false),(9,true),(25,true),(19,false),(4,false)]
theorem der_19622 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19622 :=
  CNF.rup_sound cl_19622 [cl_99,cl_115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_99 v h) (hints_cons _ _ _ (inp_115 v h) (by intro d hd; cases hd)))
def cl_19623 : CNF.NClause := [(77,true),(18,true),(17,false),(16,true),(30,true),(19,false)]
theorem der_19623 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19623 :=
  CNF.rup_sound cl_19623 [cl_1004,cl_1003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1004 v h) (hints_cons _ _ _ (inp_1003 v h) (by intro d hd; cases hd)))
def cl_19624 : CNF.NClause := [(71,true),(13,false),(7,true),(26,true),(19,false),(1,false)]
theorem der_19624 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19624 :=
  CNF.rup_sound cl_19624 [cl_611,cl_627] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_611 v h) (hints_cons _ _ _ (inp_627 v h) (by intro d hd; cases hd)))
def cl_19632 : CNF.NClause := [(90,true),(11,true),(28,true),(8,true),(19,false),(22,false)]
theorem der_19632 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19632 :=
  CNF.rup_sound cl_19632 [cl_1832,cl_1831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1832 v h) (hints_cons _ _ _ (inp_1831 v h) (by intro d hd; cases hd)))
def cl_19634 : CNF.NClause := [(115,true),(55,false),(44,false),(47,true),(59,true),(36,true)]
theorem der_19634 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19634 :=
  CNF.rup_sound cl_19634 [cl_3435,cl_3436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3435 v h) (hints_cons _ _ _ (inp_3436 v h) (by intro d hd; cases hd)))
def cl_19642 : CNF.NClause := [(80,true),(15,false),(29,false),(11,true),(7,true),(3,true)]
theorem der_19642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19642 :=
  CNF.rup_sound cl_19642 [cl_19529,cl_1176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19529 v h) (hints_cons _ _ _ (inp_1176 v h) (by intro d hd; cases hd)))
def cl_19645 : CNF.NClause := [(72,true),(13,true),(88,false),(65,false),(44,false),(78,false),(84,false)]
theorem der_19645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19645 :=
  CNF.rup_sound cl_19645 [cl_5642,cl_5646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5642 v h) (hints_cons _ _ _ (inp_5646 v h) (by intro d hd; cases hd)))
def cl_19649 : CNF.NClause := [(13,true),(84,true),(78,false),(65,false),(72,true),(88,false),(44,false)]
theorem der_19649 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19649 :=
  CNF.rup_sound cl_19649 [cl_5678,cl_5674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5678 v h) (hints_cons _ _ _ (inp_5674 v h) (by intro d hd; cases hd)))
def cl_19651 : CNF.NClause := [(13,true),(84,true),(88,false),(65,false),(72,false),(78,false),(44,false)]
theorem der_19651 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19651 :=
  CNF.rup_sound cl_19651 [cl_5670,cl_5666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5670 v h) (hints_cons _ _ _ (inp_5666 v h) (by intro d hd; cases hd)))
def cl_19655 : CNF.NClause := [(12,true),(68,true),(4,false),(29,false),(8,true),(16,true)]
theorem der_19655 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19655 :=
  CNF.rup_sound cl_19655 [cl_399,cl_415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_399 v h) (hints_cons _ _ _ (inp_415 v h) (by intro d hd; cases hd)))
def cl_19656 : CNF.NClause := [(68,true),(4,false),(29,false),(8,true),(16,true)]
theorem der_19656 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19656 :=
  CNF.rup_sound cl_19656 [cl_17664,cl_19655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17664 v h) (hints_cons _ _ _ (der_19655 v h) (by intro d hd; cases hd)))
def cl_19663 : CNF.NClause := [(89,true),(0,false),(23,false),(27,true),(7,true),(16,true)]
theorem der_19663 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19663 :=
  CNF.rup_sound cl_19663 [cl_17891,cl_1775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17891 v h) (hints_cons _ _ _ (inp_1775 v h) (by intro d hd; cases hd)))
def cl_19664 : CNF.NClause := [(81,true),(15,false),(23,false),(1,false),(9,true),(28,true)]
theorem der_19664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19664 :=
  CNF.rup_sound cl_19664 [cl_19126,cl_1255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19126 v h) (hints_cons _ _ _ (inp_1255 v h) (by intro d hd; cases hd)))
def cl_19665 : CNF.NClause := [(37,false),(70,false),(6,false),(66,false),(82,true),(78,false),(74,false)]
theorem der_19665 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19665 :=
  CNF.rup_sound cl_19665 [cl_4833,cl_17828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4833 v h) (hints_cons _ _ _ (der_17828 v h) (by intro d hd; cases hd)))
def cl_19667 : CNF.NClause := [(70,true),(17,false),(6,false),(28,true),(3,true)]
theorem der_19667 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19667 :=
  CNF.rup_sound cl_19667 [cl_19573,cl_19085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19573 v h) (hints_cons _ _ _ (der_19085 v h) (by intro d hd; cases hd)))
def cl_19668 : CNF.NClause := [(36,false),(84,false),(82,true),(83,false),(92,false),(5,true),(86,false)]
theorem der_19668 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19668 :=
  CNF.rup_sound cl_19668 [cl_4612,cl_18389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4612 v h) (hints_cons _ _ _ (der_18389 v h) (by intro d hd; cases hd)))
def cl_19687 : CNF.NClause := [(69,true),(2,false),(18,false),(11,true),(9,true),(27,true)]
theorem der_19687 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19687 :=
  CNF.rup_sound cl_19687 [cl_19512,cl_503] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19512 v h) (hints_cons _ _ _ (inp_503 v h) (by intro d hd; cases hd)))
def cl_19692 : CNF.NClause := [(72,true),(14,false),(12,false),(11,true),(30,true),(10,true)]
theorem der_19692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19692 :=
  CNF.rup_sound cl_19692 [cl_19519,cl_684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19519 v h) (hints_cons _ _ _ (inp_684 v h) (by intro d hd; cases hd)))
def cl_19693 : CNF.NClause := [(122,true),(31,false),(55,false),(43,false),(37,true),(49,false)]
theorem der_19693 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19693 :=
  CNF.rup_sound cl_19693 [cl_3875,cl_15166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3875 v h) (hints_cons _ _ _ (der_15166 v h) (by intro d hd; cases hd)))
def cl_19698 : CNF.NClause := [(84,true),(24,false),(241,false),(5,true),(28,true),(16,true),(3,true)]
theorem der_19698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19698 :=
  CNF.rup_sound cl_19698 [cl_13860,cl_13883,cl_13871,cl_19609,cl_19255,cl_13858,cl_13868,cl_8659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13860 v h) (hints_cons _ _ _ (inp_13883 v h) (hints_cons _ _ _ (inp_13871 v h) (hints_cons _ _ _ (der_19609 v h) (hints_cons _ _ _ (der_19255 v h) (hints_cons _ _ _ (inp_13858 v h) (hints_cons _ _ _ (inp_13868 v h) (hints_cons _ _ _ (inp_8659 v h) (by intro d hd; cases hd)))))))))
def cl_19702 : CNF.NClause := [(63,true),(24,false),(4,false),(25,true),(19,false),(9,true)]
theorem der_19702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19702 :=
  CNF.rup_sound cl_19702 [cl_19622,cl_103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19622 v h) (hints_cons _ _ _ (inp_103 v h) (by intro d hd; cases hd)))
def cl_19708 : CNF.NClause := [(64,true),(12,true),(7,true),(25,true),(17,false),(22,false)]
theorem der_19708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19708 :=
  CNF.rup_sound cl_19708 [cl_167,cl_168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_167 v h) (hints_cons _ _ _ (inp_168 v h) (by intro d hd; cases hd)))
def cl_19709 : CNF.NClause := [(64,true),(17,false),(25,true),(22,false),(7,true)]
theorem der_19709 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19709 :=
  CNF.rup_sound cl_19709 [cl_18786,cl_19708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18786 v h) (hints_cons _ _ _ (der_19708 v h) (by intro d hd; cases hd)))
def cl_19712 : CNF.NClause := [(489,false),(84,true),(11,true),(5,true),(28,true),(16,true)]
theorem der_19712 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19712 :=
  CNF.rup_sound cl_19712 [cl_14123,cl_14111,cl_14101,cl_14119,cl_19609,cl_19255,cl_14098,cl_14108,cl_10147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14123 v h) (hints_cons _ _ _ (inp_14111 v h) (hints_cons _ _ _ (inp_14101 v h) (hints_cons _ _ _ (inp_14119 v h) (hints_cons _ _ _ (der_19609 v h) (hints_cons _ _ _ (der_19255 v h) (hints_cons _ _ _ (inp_14098 v h) (hints_cons _ _ _ (inp_14108 v h) (hints_cons _ _ _ (inp_10147 v h) (by intro d hd; cases hd))))))))))
def cl_19713 : CNF.NClause := [(89,false),(47,false),(68,false),(66,false),(16,true),(75,true)]
theorem der_19713 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19713 :=
  CNF.rup_sound cl_19713 [cl_18311,cl_19324,cl_6074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18311 v h) (hints_cons _ _ _ (der_19324 v h) (hints_cons _ _ _ (inp_6074 v h) (by intro d hd; cases hd))))
def cl_19714 : CNF.NClause := [(89,true),(47,false),(16,true),(68,false),(75,true),(66,false),(84,true)]
theorem der_19714 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19714 :=
  CNF.rup_sound cl_19714 [cl_6122,cl_6138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6122 v h) (hints_cons _ _ _ (inp_6138 v h) (by intro d hd; cases hd)))
def cl_19715 : CNF.NClause := [(47,false),(68,false),(16,true),(66,false),(75,true)]
theorem der_19715 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19715 :=
  CNF.rup_sound cl_19715 [cl_18311,cl_19713,cl_19714] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18311 v h) (hints_cons _ _ _ (der_19713 v h) (hints_cons _ _ _ (der_19714 v h) (by intro d hd; cases hd))))
def cl_19717 : CNF.NClause := [(81,true),(23,true),(466,false),(1,false),(11,true),(9,true),(28,true)]
theorem der_19717 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19717 :=
  CNF.rup_sound cl_19717 [cl_14118,cl_14123,cl_14105,cl_19126,cl_14107,cl_1271,cl_10133,cl_14110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14118 v h) (hints_cons _ _ _ (inp_14123 v h) (hints_cons _ _ _ (inp_14105 v h) (hints_cons _ _ _ (der_19126 v h) (hints_cons _ _ _ (inp_14107 v h) (hints_cons _ _ _ (inp_1271 v h) (hints_cons _ _ _ (inp_10133 v h) (hints_cons _ _ _ (inp_14110 v h) (by intro d hd; cases hd)))))))))
def cl_19748 : CNF.NClause := [(68,true),(12,false),(4,true),(29,false),(8,true),(16,true)]
theorem der_19748 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19748 :=
  CNF.rup_sound cl_19748 [cl_17791,cl_412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17791 v h) (hints_cons _ _ _ (inp_412 v h) (by intro d hd; cases hd)))
def cl_19754 : CNF.NClause := [(122,true),(49,false),(57,true),(55,false),(43,false),(37,true)]
theorem der_19754 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19754 :=
  CNF.rup_sound cl_19754 [cl_19693,cl_3876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19693 v h) (hints_cons _ _ _ (inp_3876 v h) (by intro d hd; cases hd)))
def cl_19757 : CNF.NClause := [(48,false),(70,false),(77,false),(64,false),(76,false),(17,true),(83,false)]
theorem der_19757 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19757 :=
  CNF.rup_sound cl_19757 [cl_18279,cl_6210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18279 v h) (hints_cons _ _ _ (inp_6210 v h) (by intro d hd; cases hd)))
def cl_19758 : CNF.NClause := [(52,false),(79,false),(21,true),(66,false),(67,false),(85,false),(73,false)]
theorem der_19758 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19758 :=
  CNF.rup_sound cl_19758 [cl_6658,cl_6722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6658 v h) (hints_cons _ _ _ (inp_6722 v h) (by intro d hd; cases hd)))
def cl_19760 : CNF.NClause := [(79,true),(15,false),(449,false),(26,true),(8,true),(21,true),(10,true)]
theorem der_19760 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19760 :=
  CNF.rup_sound cl_19760 [cl_14091,cl_14074,cl_14086,cl_17836,cl_18940,cl_14068,cl_14079,cl_9932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14091 v h) (hints_cons _ _ _ (inp_14074 v h) (hints_cons _ _ _ (inp_14086 v h) (hints_cons _ _ _ (der_17836 v h) (hints_cons _ _ _ (der_18940 v h) (hints_cons _ _ _ (inp_14068 v h) (hints_cons _ _ _ (inp_14079 v h) (hints_cons _ _ _ (inp_9932 v h) (by intro d hd; cases hd)))))))))
def cl_19762 : CNF.NClause := [(71,true),(13,true),(7,true),(26,true),(19,false),(1,false)]
theorem der_19762 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19762 :=
  CNF.rup_sound cl_19762 [cl_615,cl_631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_615 v h) (hints_cons _ _ _ (inp_631 v h) (by intro d hd; cases hd)))
def cl_19763 : CNF.NClause := [(71,true),(1,false),(7,true),(26,true),(19,false)]
theorem der_19763 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19763 :=
  CNF.rup_sound cl_19763 [cl_19624,cl_19762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19624 v h) (hints_cons _ _ _ (der_19762 v h) (by intro d hd; cases hd)))
def cl_19765 : CNF.NClause := [(70,true),(17,true),(409,false),(9,true),(6,false),(28,true),(3,true)]
theorem der_19765 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19765 :=
  CNF.rup_sound cl_19765 [cl_14052,cl_14063,cl_14039,cl_19573,cl_14049,cl_558,cl_9694,cl_14055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14052 v h) (hints_cons _ _ _ (inp_14063 v h) (hints_cons _ _ _ (inp_14039 v h) (hints_cons _ _ _ (der_19573 v h) (hints_cons _ _ _ (inp_14049 v h) (hints_cons _ _ _ (inp_558 v h) (hints_cons _ _ _ (inp_9694 v h) (hints_cons _ _ _ (inp_14055 v h) (by intro d hd; cases hd)))))))))
def cl_19778 : CNF.NClause := [(64,true),(12,true),(22,false),(25,false),(7,true),(17,true)]
theorem der_19778 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19778 :=
  CNF.rup_sound cl_19778 [cl_143,cl_144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_143 v h) (hints_cons _ _ _ (inp_144 v h) (by intro d hd; cases hd)))
def cl_19779 : CNF.NClause := [(64,true),(17,true),(25,false),(22,false),(7,true)]
theorem der_19779 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19779 :=
  CNF.rup_sound cl_19779 [cl_18786,cl_19778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18786 v h) (hints_cons _ _ _ (der_19778 v h) (by intro d hd; cases hd)))
def cl_19782 : CNF.NClause := [(81,true),(1,false),(23,false),(12,true),(9,true),(28,true)]
theorem der_19782 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19782 :=
  CNF.rup_sound cl_19782 [cl_19664,cl_1263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19664 v h) (hints_cons _ _ _ (inp_1263 v h) (by intro d hd; cases hd)))
def cl_19783 : CNF.NClause := [(80,true),(24,false),(29,false),(11,true),(7,true),(3,true)]
theorem der_19783 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19783 :=
  CNF.rup_sound cl_19783 [cl_19529,cl_1168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19529 v h) (hints_cons _ _ _ (inp_1168 v h) (by intro d hd; cases hd)))
def cl_19785 : CNF.NClause := [(77,true),(18,false),(30,true),(16,true),(17,true),(19,false)]
theorem der_19785 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19785 :=
  CNF.rup_sound cl_19785 [cl_999,cl_1000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_999 v h) (hints_cons _ _ _ (inp_1000 v h) (by intro d hd; cases hd)))
def cl_19799 : CNF.NClause := [(14,true),(89,true),(45,false),(63,false),(72,false),(70,false),(86,false)]
theorem der_19799 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19799 :=
  CNF.rup_sound cl_19799 [cl_18186,cl_18093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18186 v h) (hints_cons _ _ _ (der_18093 v h) (by intro d hd; cases hd)))
def cl_19806 : CNF.NClause := [(63,true),(24,false),(4,false),(25,false),(19,false),(9,true)]
theorem der_19806 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19806 :=
  CNF.rup_sound cl_19806 [cl_15417,cl_71] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15417 v h) (hints_cons _ _ _ (inp_71 v h) (by intro d hd; cases hd)))
def cl_19807 : CNF.NClause := [(69,true),(452,false),(18,false),(11,true),(9,true),(27,true),(10,true)]
theorem der_19807 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19807 :=
  CNF.rup_sound cl_19807 [cl_14076,cl_14075,cl_14092,cl_19512,cl_19687,cl_14085,cl_14068,cl_9872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14076 v h) (hints_cons _ _ _ (inp_14075 v h) (hints_cons _ _ _ (inp_14092 v h) (hints_cons _ _ _ (der_19512 v h) (hints_cons _ _ _ (der_19687 v h) (hints_cons _ _ _ (inp_14085 v h) (hints_cons _ _ _ (inp_14068 v h) (hints_cons _ _ _ (inp_9872 v h) (by intro d hd; cases hd)))))))))
def cl_19811 : CNF.NClause := [(29,true),(74,true),(6,false),(23,true),(10,true),(19,false)]
theorem der_19811 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19811 :=
  CNF.rup_sound cl_19811 [cl_822,cl_821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_822 v h) (hints_cons _ _ _ (inp_821 v h) (by intro d hd; cases hd)))
def cl_19812 : CNF.NClause := [(29,false),(74,true),(23,true),(10,true),(19,false),(6,false)]
theorem der_19812 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19812 :=
  CNF.rup_sound cl_19812 [cl_789,cl_790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_789 v h) (hints_cons _ _ _ (inp_790 v h) (by intro d hd; cases hd)))
def cl_19813 : CNF.NClause := [(74,true),(23,true),(6,false),(19,false),(10,true)]
theorem der_19813 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19813 :=
  CNF.rup_sound cl_19813 [cl_19811,cl_19812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19811 v h) (hints_cons _ _ _ (der_19812 v h) (by intro d hd; cases hd)))
def cl_19814 : CNF.NClause := [(24,true),(63,true),(9,true),(25,false),(19,false),(4,false)]
theorem der_19814 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19814 :=
  CNF.rup_sound cl_19814 [cl_87,cl_83] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_87 v h) (hints_cons _ _ _ (inp_83 v h) (by intro d hd; cases hd)))
def cl_19815 : CNF.NClause := [(63,true),(4,false),(9,true),(25,false),(19,false)]
theorem der_19815 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19815 :=
  CNF.rup_sound cl_19815 [cl_19806,cl_19814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19806 v h) (hints_cons _ _ _ (der_19814 v h) (by intro d hd; cases hd)))
def cl_19823 : CNF.NClause := [(123,true),(41,true),(36,true),(56,false),(51,false)]
theorem der_19823 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19823 :=
  CNF.rup_sound cl_19823 [cl_19437,cl_19240,cl_3920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19437 v h) (hints_cons _ _ _ (der_19240 v h) (hints_cons _ _ _ (inp_3920 v h) (by intro d hd; cases hd))))
def cl_19825 : CNF.NClause := [(118,true),(31,false),(32,false),(61,true),(34,true),(35,true)]
theorem der_19825 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19825 :=
  CNF.rup_sound cl_19825 [cl_3645,cl_19154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3645 v h) (hints_cons _ _ _ (der_19154 v h) (by intro d hd; cases hd)))
def cl_19829 : CNF.NClause := [(96,true),(39,true),(56,false),(44,false),(49,true),(54,true)]
theorem der_19829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19829 :=
  CNF.rup_sound cl_19829 [cl_2203,cl_2204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2203 v h) (hints_cons _ _ _ (inp_2204 v h) (by intro d hd; cases hd)))
def cl_19833 : CNF.NClause := [(24,true),(63,true),(25,false),(4,true),(19,false),(9,true)]
theorem der_19833 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19833 :=
  CNF.rup_sound cl_19833 [cl_84,cl_88] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_84 v h) (hints_cons _ _ _ (inp_88 v h) (by intro d hd; cases hd)))
def cl_19834 : CNF.NClause := [(24,false),(63,true),(9,true),(25,false),(19,false),(4,true)]
theorem der_19834 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19834 :=
  CNF.rup_sound cl_19834 [cl_72,cl_15417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_72 v h) (hints_cons _ _ _ (der_15417 v h) (by intro d hd; cases hd)))
def cl_19835 : CNF.NClause := [(63,true),(4,true),(25,false),(9,true),(19,false)]
theorem der_19835 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19835 :=
  CNF.rup_sound cl_19835 [cl_19833,cl_19834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19833 v h) (hints_cons _ _ _ (der_19834 v h) (by intro d hd; cases hd)))
def cl_19851 : CNF.NClause := [(71,true),(20,false),(13,true),(19,false),(26,true),(7,true)]
theorem der_19851 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19851 :=
  CNF.rup_sound cl_19851 [cl_19763,cl_616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19763 v h) (hints_cons _ _ _ (inp_616 v h) (by intro d hd; cases hd)))
def cl_19854 : CNF.NClause := [(74,true),(29,true),(6,false),(23,false),(10,true),(19,false)]
theorem der_19854 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19854 :=
  CNF.rup_sound cl_19854 [cl_806,cl_805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_806 v h) (hints_cons _ _ _ (inp_805 v h) (by intro d hd; cases hd)))
def cl_19855 : CNF.NClause := [(74,true),(23,false),(19,false),(6,false),(10,true)]
theorem der_19855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19855 :=
  CNF.rup_sound cl_19855 [cl_15412,cl_19854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15412 v h) (hints_cons _ _ _ (der_19854 v h) (by intro d hd; cases hd)))
def cl_19858 : CNF.NClause := [(91,true),(12,false),(26,true),(6,false)]
theorem der_19858 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19858 :=
  CNF.rup_sound cl_19858 [cl_18359,cl_18462] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18359 v h) (hints_cons _ _ _ (der_18462 v h) (by intro d hd; cases hd)))
def cl_19866 : CNF.NClause := [(81,true),(1,true),(9,true),(12,false),(28,true),(23,false)]
theorem der_19866 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19866 :=
  CNF.rup_sound cl_19866 [cl_1260,cl_19129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1260 v h) (hints_cons _ _ _ (der_19129 v h) (by intro d hd; cases hd)))
def cl_19867 : CNF.NClause := [(81,true),(23,false),(12,false),(9,true),(28,true)]
theorem der_19867 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19867 :=
  CNF.rup_sound cl_19867 [cl_19126,cl_19866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19126 v h) (hints_cons _ _ _ (der_19866 v h) (by intro d hd; cases hd)))
def cl_19869 : CNF.NClause := [(71,true),(20,true),(13,false),(19,false),(26,true),(7,true)]
theorem der_19869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19869 :=
  CNF.rup_sound cl_19869 [cl_19763,cl_628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19763 v h) (hints_cons _ _ _ (inp_628 v h) (by intro d hd; cases hd)))
def cl_19878 : CNF.NClause := [(93,true),(56,false),(61,true),(57,true),(59,true),(60,false)]
theorem der_19878 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19878 :=
  CNF.rup_sound cl_19878 [cl_2027,cl_2031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2027 v h) (hints_cons _ _ _ (inp_2031 v h) (by intro d hd; cases hd)))
def cl_19882 : CNF.NClause := [(71,true),(20,false),(13,false),(19,false),(26,true),(7,true)]
theorem der_19882 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19882 :=
  CNF.rup_sound cl_19882 [cl_19763,cl_612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19763 v h) (hints_cons _ _ _ (inp_612 v h) (by intro d hd; cases hd)))
def cl_19891 : CNF.NClause := [(71,true),(13,false),(7,true),(19,false),(26,true)]
theorem der_19891 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19891 :=
  CNF.rup_sound cl_19891 [cl_19869,cl_19882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19869 v h) (hints_cons _ _ _ (der_19882 v h) (by intro d hd; cases hd)))
def cl_19895 : CNF.NClause := [(120,true),(31,false),(45,true),(38,true),(47,true),(54,false)]
theorem der_19895 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19895 :=
  CNF.rup_sound cl_19895 [cl_3727,cl_3759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3727 v h) (hints_cons _ _ _ (inp_3759 v h) (by intro d hd; cases hd)))
def cl_19906 : CNF.NClause := [(74,true),(6,false),(10,true),(19,false)]
theorem der_19906 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19906 :=
  CNF.rup_sound cl_19906 [cl_19813,cl_19855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19813 v h) (hints_cons _ _ _ (der_19855 v h) (by intro d hd; cases hd)))
def cl_19909 : CNF.NClause := [(81,true),(89,false),(54,false),(67,false),(74,false),(65,false),(83,false)]
theorem der_19909 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19909 :=
  CNF.rup_sound cl_19909 [cl_6930,cl_6929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6930 v h) (hints_cons _ _ _ (inp_6929 v h) (by intro d hd; cases hd)))
def cl_19912 : CNF.NClause := [(91,true),(12,true),(6,false),(26,true),(18,true),(24,false)]
theorem der_19912 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19912 :=
  CNF.rup_sound cl_19912 [cl_1902,cl_1901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1902 v h) (hints_cons _ _ _ (inp_1901 v h) (by intro d hd; cases hd)))
def cl_19914 : CNF.NClause := [(91,true),(12,true),(6,false),(26,true),(18,false),(24,false)]
theorem der_19914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19914 :=
  CNF.rup_sound cl_19914 [cl_1894,cl_1893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1894 v h) (hints_cons _ _ _ (inp_1893 v h) (by intro d hd; cases hd)))
def cl_19915 : CNF.NClause := [(91,true),(18,false),(24,false),(26,true),(6,false)]
theorem der_19915 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19915 :=
  CNF.rup_sound cl_19915 [cl_19858,cl_19914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19858 v h) (hints_cons _ _ _ (der_19914 v h) (by intro d hd; cases hd)))
def cl_19920 : CNF.NClause := [(4,true),(12,true),(68,false),(8,true),(20,true),(16,true)]
theorem der_19920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19920 :=
  CNF.rup_sound cl_19920 [cl_416,cl_448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_416 v h) (hints_cons _ _ _ (inp_448 v h) (by intro d hd; cases hd)))
def cl_19922 : CNF.NClause := [(77,true),(18,false),(30,true),(16,true),(17,false),(19,false)]
theorem der_19922 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19922 :=
  CNF.rup_sound cl_19922 [cl_995,cl_996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_995 v h) (hints_cons _ _ _ (inp_996 v h) (by intro d hd; cases hd)))
def cl_19927 : CNF.NClause := [(63,true),(25,false),(9,true),(19,false)]
theorem der_19927 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19927 :=
  CNF.rup_sound cl_19927 [cl_19815,cl_19835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19815 v h) (hints_cons _ _ _ (der_19835 v h) (by intro d hd; cases hd)))
def cl_19931 : CNF.NClause := [(0,true),(91,false),(92,false),(31,false),(88,false),(90,false)]
theorem der_19931 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19931 :=
  CNF.rup_sound cl_19931 [cl_18636,cl_14845,cl_3980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18636 v h) (hints_cons _ _ _ (der_14845 v h) (hints_cons _ _ _ (inp_3980 v h) (by intro d hd; cases hd))))
def cl_19933 : CNF.NClause := [(118,true),(33,true),(34,true),(31,false),(35,false),(61,true)]
theorem der_19933 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19933 :=
  CNF.rup_sound cl_19933 [cl_3631,cl_18554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3631 v h) (hints_cons _ _ _ (der_18554 v h) (by intro d hd; cases hd)))
def cl_19943 : CNF.NClause := [(58,true),(109,true),(35,false),(44,false),(53,true),(37,true)]
theorem der_19943 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19943 :=
  CNF.rup_sound cl_19943 [cl_18862,cl_3067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18862 v h) (hints_cons _ _ _ (inp_3067 v h) (by intro d hd; cases hd)))
def cl_19944 : CNF.NClause := [(58,false),(76,false),(27,true),(89,false),(69,false),(78,false),(85,false)]
theorem der_19944 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19944 :=
  CNF.rup_sound cl_19944 [cl_7428,cl_7426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7428 v h) (hints_cons _ _ _ (inp_7426 v h) (by intro d hd; cases hd)))
def cl_19945 : CNF.NClause := [(101,true),(48,false),(51,true),(37,true),(59,true),(45,false)]
theorem der_19945 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19945 :=
  CNF.rup_sound cl_19945 [cl_2547,cl_2548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2547 v h) (hints_cons _ _ _ (inp_2548 v h) (by intro d hd; cases hd)))
def cl_19946 : CNF.NClause := [(108,true),(48,false),(47,true),(61,true),(50,false),(49,false)]
theorem der_19946 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19946 :=
  CNF.rup_sound cl_19946 [cl_2980,cl_18985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2980 v h) (hints_cons _ _ _ (der_18985 v h) (by intro d hd; cases hd)))
def cl_19947 : CNF.NClause := [(95,true),(48,false),(53,true),(43,false),(33,false),(38,true)]
theorem der_19947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19947 :=
  CNF.rup_sound cl_19947 [cl_2131,cl_2163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2131 v h) (hints_cons _ _ _ (inp_2163 v h) (by intro d hd; cases hd)))
def cl_19957 : CNF.NClause := [(94,true),(35,false),(55,false),(45,true),(40,true),(50,true)]
theorem der_19957 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19957 :=
  CNF.rup_sound cl_19957 [cl_18382,cl_2095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18382 v h) (hints_cons _ _ _ (inp_2095 v h) (by intro d hd; cases hd)))
def cl_19958 : CNF.NClause := [(118,true),(35,false),(61,true),(33,false),(34,true),(31,false)]
theorem der_19958 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19958 :=
  CNF.rup_sound cl_19958 [cl_3627,cl_19154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3627 v h) (hints_cons _ _ _ (der_19154 v h) (by intro d hd; cases hd)))
def cl_19966 : CNF.NClause := [(107,true),(41,true),(55,false),(48,false),(58,true),(39,true)]
theorem der_19966 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19966 :=
  CNF.rup_sound cl_19966 [cl_18121,cl_2920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18121 v h) (hints_cons _ _ _ (inp_2920 v h) (by intro d hd; cases hd)))
def cl_19970 : CNF.NClause := [(77,true),(17,false),(19,false),(16,true),(30,true)]
theorem der_19970 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19970 :=
  CNF.rup_sound cl_19970 [cl_19623,cl_19922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19623 v h) (hints_cons _ _ _ (der_19922 v h) (by intro d hd; cases hd)))
def cl_19972 : CNF.NClause := [(94,true),(55,false),(35,false),(50,true),(40,true),(45,false)]
theorem der_19972 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19972 :=
  CNF.rup_sound cl_19972 [cl_2091,cl_19134] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2091 v h) (hints_cons _ _ _ (der_19134 v h) (by intro d hd; cases hd)))
def cl_19973 : CNF.NClause := [(94,true),(35,false),(50,true),(45,false),(40,true)]
theorem der_19973 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19973 :=
  CNF.rup_sound cl_19973 [cl_18975,cl_19972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18975 v h) (hints_cons _ _ _ (der_19972 v h) (by intro d hd; cases hd)))
def cl_19979 : CNF.NClause := [(65,true),(13,false),(25,false),(8,true),(3,true)]
theorem der_19979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19979 :=
  CNF.rup_sound cl_19979 [cl_18267,cl_19601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18267 v h) (hints_cons _ _ _ (der_19601 v h) (by intro d hd; cases hd)))
def cl_19981 : CNF.NClause := [(87,true),(89,false),(0,false),(31,false),(92,false),(90,false),(88,false)]
theorem der_19981 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19981 :=
  CNF.rup_sound cl_19981 [cl_3971,cl_4003] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3971 v h) (hints_cons _ _ _ (inp_4003 v h) (by intro d hd; cases hd)))
def cl_19984 : CNF.NClause := [(122,true),(49,false),(43,false),(57,true),(31,false),(37,true)]
theorem der_19984 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19984 :=
  CNF.rup_sound cl_19984 [cl_19693,cl_3891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19693 v h) (hints_cons _ _ _ (inp_3891 v h) (by intro d hd; cases hd)))
def cl_19985 : CNF.NClause := [(108,true),(48,true),(47,true),(49,false),(61,true),(50,false)]
theorem der_19985 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19985 :=
  CNF.rup_sound cl_19985 [cl_2984,cl_18948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2984 v h) (hints_cons _ _ _ (der_18948 v h) (by intro d hd; cases hd)))
def cl_19986 : CNF.NClause := [(108,true),(49,false),(47,true),(61,true),(50,false)]
theorem der_19986 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19986 :=
  CNF.rup_sound cl_19986 [cl_19946,cl_19985] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19946 v h) (hints_cons _ _ _ (der_19985 v h) (by intro d hd; cases hd)))
def cl_19987 : CNF.NClause := [(41,false),(73,false),(75,true),(72,false),(10,true),(74,false),(92,false)]
theorem der_19987 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19987 :=
  CNF.rup_sound cl_19987 [cl_5266,cl_5298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5266 v h) (hints_cons _ _ _ (inp_5298 v h) (by intro d hd; cases hd)))
def cl_19988 : CNF.NClause := [(100,true),(49,false),(51,false),(40,true),(33,true),(42,true)]
theorem der_19988 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19988 :=
  CNF.rup_sound cl_19988 [cl_2472,cl_2440] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2472 v h) (hints_cons _ _ _ (inp_2440 v h) (by intro d hd; cases hd)))
def cl_19992 : CNF.NClause := [(34,false),(87,false),(75,true),(3,true),(70,false),(85,false),(65,false)]
theorem der_19992 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19992 :=
  CNF.rup_sound cl_19992 [cl_4362,cl_4378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4362 v h) (hints_cons _ _ _ (inp_4378 v h) (by intro d hd; cases hd)))
def cl_19993 : CNF.NClause := [(123,true),(41,true),(36,true),(51,false),(31,false)]
theorem der_19993 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19993 :=
  CNF.rup_sound cl_19993 [cl_19437,cl_19240,cl_3951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19437 v h) (hints_cons _ _ _ (der_19240 v h) (hints_cons _ _ _ (inp_3951 v h) (by intro d hd; cases hd))))
def cl_19994 : CNF.NClause := [(121,true),(59,true),(50,false),(53,true),(31,false),(42,true)]
theorem der_19994 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19994 :=
  CNF.rup_sound cl_19994 [cl_3831,cl_3829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3831 v h) (hints_cons _ _ _ (inp_3829 v h) (by intro d hd; cases hd)))
def cl_19995 : CNF.NClause := [(52,false),(73,false),(85,false),(88,false),(66,false),(67,false),(21,true)]
theorem der_19995 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19995 :=
  CNF.rup_sound cl_19995 [cl_19758,cl_6674] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19758 v h) (hints_cons _ _ _ (inp_6674 v h) (by intro d hd; cases hd)))
def cl_19997 : CNF.NClause := [(120,true),(45,false),(38,true),(31,false),(47,true),(54,false)]
theorem der_19997 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19997 :=
  CNF.rup_sound cl_19997 [cl_3723,cl_3755] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3723 v h) (hints_cons _ _ _ (inp_3755 v h) (by intro d hd; cases hd)))
def cl_19999 : CNF.NClause := [(118,true),(35,false),(61,true),(31,false),(34,true)]
theorem der_19999 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_19999 :=
  CNF.rup_sound cl_19999 [cl_19958,cl_19933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19958 v h) (hints_cons _ _ _ (der_19933 v h) (by intro d hd; cases hd)))
def cl_20001 : CNF.NClause := [(120,true),(31,false),(54,false),(38,true),(47,true)]
theorem der_20001 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20001 :=
  CNF.rup_sound cl_20001 [cl_19895,cl_19997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19895 v h) (hints_cons _ _ _ (der_19997 v h) (by intro d hd; cases hd)))
def cl_20004 : CNF.NClause := [(122,true),(49,true),(43,false),(37,true),(31,false),(57,true)]
theorem der_20004 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20004 :=
  CNF.rup_sound cl_20004 [cl_3883,cl_3899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3883 v h) (hints_cons _ _ _ (inp_3899 v h) (by intro d hd; cases hd)))
def cl_20005 : CNF.NClause := [(52,false),(73,true),(21,true),(66,false),(67,false),(85,false),(88,false)]
theorem der_20005 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20005 :=
  CNF.rup_sound cl_20005 [cl_6666,cl_6682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6666 v h) (hints_cons _ _ _ (inp_6682 v h) (by intro d hd; cases hd)))
def cl_20006 : CNF.NClause := [(41,false),(73,true),(10,true),(74,false),(72,false),(75,true),(92,false)]
theorem der_20006 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20006 :=
  CNF.rup_sound cl_20006 [cl_5270,cl_5302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5270 v h) (hints_cons _ _ _ (inp_5302 v h) (by intro d hd; cases hd)))
def cl_20016 : CNF.NClause := [(18,true),(73,false),(7,true),(10,true),(28,true),(21,true)]
theorem der_20016 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20016 :=
  CNF.rup_sound cl_20016 [cl_767,cl_768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_767 v h) (hints_cons _ _ _ (inp_768 v h) (by intro d hd; cases hd)))
def cl_20025 : CNF.NClause := [(12,true),(72,false),(30,true),(10,true),(11,true),(13,true)]
theorem der_20025 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20025 :=
  CNF.rup_sound cl_20025 [cl_688,cl_704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_688 v h) (hints_cons _ _ _ (inp_704 v h) (by intro d hd; cases hd)))
def cl_20027 : CNF.NClause := [(483,false),(73,true),(11,true),(28,true),(7,true),(21,true),(10,true)]
theorem der_20027 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20027 :=
  CNF.rup_sound cl_20027 [cl_14123,cl_14116,cl_14103,cl_14106,cl_14113,cl_10082,cl_759,cl_14100] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14123 v h) (hints_cons _ _ _ (inp_14116 v h) (hints_cons _ _ _ (inp_14103 v h) (hints_cons _ _ _ (inp_14106 v h) (hints_cons _ _ _ (inp_14113 v h) (hints_cons _ _ _ (inp_10082 v h) (hints_cons _ _ _ (inp_759 v h) (hints_cons _ _ _ (inp_14100 v h) (by intro d hd; cases hd)))))))))
def cl_20029 : CNF.NClause := [(121,true),(59,false),(31,false),(42,true),(50,false),(53,true)]
theorem der_20029 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20029 :=
  CNF.rup_sound cl_20029 [cl_3797,cl_3799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3797 v h) (hints_cons _ _ _ (inp_3799 v h) (by intro d hd; cases hd)))
def cl_20030 : CNF.NClause := [(121,true),(42,true),(50,false),(53,true),(31,false)]
theorem der_20030 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20030 :=
  CNF.rup_sound cl_20030 [cl_19994,cl_20029] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19994 v h) (hints_cons _ _ _ (der_20029 v h) (by intro d hd; cases hd)))
def cl_20031 : CNF.NClause := [(73,false),(84,true),(28,true),(70,false),(90,false),(81,false),(59,false)]
theorem der_20031 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20031 :=
  CNF.rup_sound cl_20031 [cl_7588,cl_19323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7588 v h) (hints_cons _ _ _ (der_19323 v h) (by intro d hd; cases hd)))
def cl_20035 : CNF.NClause := [(65,true),(81,false),(74,false),(83,false),(54,false),(67,false)]
theorem der_20035 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20035 :=
  CNF.rup_sound cl_20035 [cl_18787,cl_18798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18787 v h) (hints_cons _ _ _ (der_18798 v h) (by intro d hd; cases hd)))
def cl_20044 : CNF.NClause := [(36,false),(85,false),(83,false),(86,false),(5,true),(82,true),(92,false)]
theorem der_20044 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20044 :=
  CNF.rup_sound cl_20044 [cl_19668,cl_4620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19668 v h) (hints_cons _ _ _ (inp_4620 v h) (by intro d hd; cases hd)))
def cl_20053 : CNF.NClause := [(41,false),(72,false),(75,true),(92,false),(10,true),(74,false)]
theorem der_20053 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20053 :=
  CNF.rup_sound cl_20053 [cl_19987,cl_20006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19987 v h) (hints_cons _ _ _ (der_20006 v h) (by intro d hd; cases hd)))
def cl_20062 : CNF.NClause := [(61,false),(87,false),(30,true),(77,false),(67,false),(72,true),(82,true)]
theorem der_20062 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20062 :=
  CNF.rup_sound cl_20062 [cl_7850,cl_7852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7850 v h) (hints_cons _ _ _ (inp_7852 v h) (by intro d hd; cases hd)))
def cl_20069 : CNF.NClause := [(41,false),(76,false),(92,false),(74,false),(10,true),(75,true),(72,true)]
theorem der_20069 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20069 :=
  CNF.rup_sound cl_20069 [cl_5268,cl_5272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5268 v h) (hints_cons _ _ _ (inp_5272 v h) (by intro d hd; cases hd)))
def cl_20077 : CNF.NClause := [(96,true),(56,false),(54,false),(34,true),(39,true),(44,true)]
theorem der_20077 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20077 :=
  CNF.rup_sound cl_20077 [cl_2192,cl_19414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2192 v h) (hints_cons _ _ _ (der_19414 v h) (by intro d hd; cases hd)))
def cl_20086 : CNF.NClause := [(80,false),(89,false),(71,false),(38,false),(64,false),(82,true),(7,true)]
theorem der_20086 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20086 :=
  CNF.rup_sound cl_20086 [cl_18300,cl_4906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18300 v h) (hints_cons _ _ _ (inp_4906 v h) (by intro d hd; cases hd)))
def cl_20087 : CNF.NClause := [(80,true),(89,false),(7,true),(71,false),(64,false),(38,false),(82,true)]
theorem der_20087 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20087 :=
  CNF.rup_sound cl_20087 [cl_4922,cl_4914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4922 v h) (hints_cons _ _ _ (inp_4914 v h) (by intro d hd; cases hd)))
def cl_20088 : CNF.NClause := [(89,false),(71,false),(7,true),(38,false),(64,false),(82,true)]
theorem der_20088 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20088 :=
  CNF.rup_sound cl_20088 [cl_20086,cl_20087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20086 v h) (hints_cons _ _ _ (der_20087 v h) (by intro d hd; cases hd)))
def cl_20089 : CNF.NClause := [(80,true),(38,false),(7,true),(71,false),(64,false),(89,true),(82,true)]
theorem der_20089 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20089 :=
  CNF.rup_sound cl_20089 [cl_4986,cl_4978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4986 v h) (hints_cons _ _ _ (inp_4978 v h) (by intro d hd; cases hd)))
def cl_20090 : CNF.NClause := [(38,false),(71,false),(7,true),(82,true),(64,false),(89,true)]
theorem der_20090 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20090 :=
  CNF.rup_sound cl_20090 [cl_20089,cl_18300,cl_4970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20089 v h) (hints_cons _ _ _ (der_18300 v h) (hints_cons _ _ _ (inp_4970 v h) (by intro d hd; cases hd))))
def cl_20091 : CNF.NClause := [(71,false),(38,false),(7,true),(82,true),(64,false)]
theorem der_20091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20091 :=
  CNF.rup_sound cl_20091 [cl_20088,cl_20090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20088 v h) (hints_cons _ _ _ (der_20090 v h) (by intro d hd; cases hd)))
def cl_20093 : CNF.NClause := [(81,false),(83,false),(89,true),(54,false),(74,false),(67,false)]
theorem der_20093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20093 :=
  CNF.rup_sound cl_20093 [cl_20035,cl_18548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20035 v h) (hints_cons _ _ _ (der_18548 v h) (by intro d hd; cases hd)))
def cl_20094 : CNF.NClause := [(23,true),(81,true),(54,false),(67,false),(74,false),(89,true),(83,false)]
theorem der_20094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20094 :=
  CNF.rup_sound cl_20094 [cl_6994,cl_6996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6994 v h) (hints_cons _ _ _ (inp_6996 v h) (by intro d hd; cases hd)))
def cl_20095 : CNF.NClause := [(23,false),(81,true),(89,true),(54,false),(74,false),(67,false),(83,false)]
theorem der_20095 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20095 :=
  CNF.rup_sound cl_20095 [cl_6993,cl_6995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6993 v h) (hints_cons _ _ _ (inp_6995 v h) (by intro d hd; cases hd)))
def cl_20096 : CNF.NClause := [(81,true),(83,false),(54,false),(67,false),(74,false),(89,true)]
theorem der_20096 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20096 :=
  CNF.rup_sound cl_20096 [cl_20094,cl_20095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20094 v h) (hints_cons _ _ _ (der_20095 v h) (by intro d hd; cases hd)))
def cl_20097 : CNF.NClause := [(83,false),(89,true),(67,false),(54,false),(74,false)]
theorem der_20097 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20097 :=
  CNF.rup_sound cl_20097 [cl_20093,cl_20096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20093 v h) (hints_cons _ _ _ (der_20096 v h) (by intro d hd; cases hd)))
def cl_20098 : CNF.NClause := [(81,true),(89,true),(23,true),(83,true),(67,false),(74,false),(54,false)]
theorem der_20098 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20098 :=
  CNF.rup_sound cl_20098 [cl_7028,cl_7026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7028 v h) (hints_cons _ _ _ (inp_7026 v h) (by intro d hd; cases hd)))
def cl_20099 : CNF.NClause := [(81,false),(83,true),(54,false),(67,false),(74,false),(89,true),(23,true)]
theorem der_20099 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20099 :=
  CNF.rup_sound cl_20099 [cl_7010,cl_7012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7010 v h) (hints_cons _ _ _ (inp_7012 v h) (by intro d hd; cases hd)))
def cl_20100 : CNF.NClause := [(89,true),(23,true),(54,false),(83,true),(67,false),(74,false)]
theorem der_20100 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20100 :=
  CNF.rup_sound cl_20100 [cl_20098,cl_20099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20098 v h) (hints_cons _ _ _ (der_20099 v h) (by intro d hd; cases hd)))
def cl_20102 : CNF.NClause := [(81,false),(23,true),(67,false),(54,false),(74,false),(89,false),(83,true)]
theorem der_20102 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20102 :=
  CNF.rup_sound cl_20102 [cl_6948,cl_6946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6948 v h) (hints_cons _ _ _ (inp_6946 v h) (by intro d hd; cases hd)))
def cl_20103 : CNF.NClause := [(81,true),(23,true),(89,false),(83,true),(67,false),(74,false),(54,false)]
theorem der_20103 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20103 :=
  CNF.rup_sound cl_20103 [cl_6964,cl_6962] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6964 v h) (hints_cons _ _ _ (inp_6962 v h) (by intro d hd; cases hd)))
def cl_20104 : CNF.NClause := [(23,true),(83,true),(67,false),(54,false),(74,false),(89,false)]
theorem der_20104 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20104 :=
  CNF.rup_sound cl_20104 [cl_20102,cl_20103] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20102 v h) (hints_cons _ _ _ (der_20103 v h) (by intro d hd; cases hd)))
def cl_20107 : CNF.NClause := [(18,true),(91,true),(0,false),(12,true),(26,true),(6,false)]
theorem der_20107 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20107 :=
  CNF.rup_sound cl_20107 [cl_19912,cl_1917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19912 v h) (hints_cons _ _ _ (inp_1917 v h) (by intro d hd; cases hd)))
def cl_20108 : CNF.NClause := [(18,false),(91,true),(0,false),(26,true),(12,true),(6,false)]
theorem der_20108 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20108 :=
  CNF.rup_sound cl_20108 [cl_1909,cl_19914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1909 v h) (hints_cons _ _ _ (der_19914 v h) (by intro d hd; cases hd)))
def cl_20109 : CNF.NClause := [(91,true),(0,false),(6,false),(12,true),(26,true)]
theorem der_20109 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20109 :=
  CNF.rup_sound cl_20109 [cl_20107,cl_20108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20107 v h) (hints_cons _ _ _ (der_20108 v h) (by intro d hd; cases hd)))
def cl_20121 : CNF.NClause := [(122,true),(49,false),(31,true),(57,true),(37,true),(43,false)]
theorem der_20121 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20121 :=
  CNF.rup_sound cl_20121 [cl_3876,cl_3892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3876 v h) (hints_cons _ _ _ (inp_3892 v h) (by intro d hd; cases hd)))
def cl_20123 : CNF.NClause := [(100,true),(51,false),(49,false),(58,true),(42,true),(40,true)]
theorem der_20123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20123 :=
  CNF.rup_sound cl_20123 [cl_18277,cl_19988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18277 v h) (hints_cons _ _ _ (der_19988 v h) (by intro d hd; cases hd)))
def cl_20124 : CNF.NClause := [(39,false),(76,false),(82,true),(8,true),(68,false),(90,false)]
theorem der_20124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20124 :=
  CNF.rup_sound cl_20124 [cl_19375,cl_17841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19375 v h) (hints_cons _ _ _ (der_17841 v h) (by intro d hd; cases hd)))
def cl_20136 : CNF.NClause := [(12,true),(23,true),(9,true),(28,true),(1,true),(81,false)]
theorem der_20136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20136 :=
  CNF.rup_sound cl_20136 [cl_1280,cl_1272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1280 v h) (hints_cons _ _ _ (inp_1272 v h) (by intro d hd; cases hd)))
def cl_20138 : CNF.NClause := [(119,true),(48,true),(31,false),(40,true),(52,true),(60,false)]
theorem der_20138 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20138 :=
  CNF.rup_sound cl_20138 [cl_3679,cl_18610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3679 v h) (hints_cons _ _ _ (der_18610 v h) (by intro d hd; cases hd)))
def cl_20142 : CNF.NClause := [(23,false),(89,false),(81,false),(83,false),(54,true),(25,false),(74,false),(67,false),(8,true),(3,true)]
theorem der_20142 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20142 :=
  CNF.rup_sound cl_20142 [cl_6913,cl_19422,cl_19601,cl_208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6913 v h) (hints_cons _ _ _ (der_19422 v h) (hints_cons _ _ _ (der_19601 v h) (hints_cons _ _ _ (inp_208 v h) (by intro d hd; cases hd)))))
def cl_20167 : CNF.NClause := [(65,true),(18,false),(23,true),(25,false),(8,true),(3,true)]
theorem der_20167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20167 :=
  CNF.rup_sound cl_20167 [cl_19979,cl_216] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19979 v h) (hints_cons _ _ _ (inp_216 v h) (by intro d hd; cases hd)))
def cl_20169 : CNF.NClause := [(45,false),(120,true),(54,true),(38,true),(47,true),(31,false)]
theorem der_20169 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20169 :=
  CNF.rup_sound cl_20169 [cl_3771,cl_3739] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3771 v h) (hints_cons _ _ _ (inp_3739 v h) (by intro d hd; cases hd)))
def cl_20171 : CNF.NClause := [(40,false),(88,false),(81,false),(63,false),(9,true),(82,true),(75,true)]
theorem der_20171 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20171 :=
  CNF.rup_sound cl_20171 [cl_18498,cl_5166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18498 v h) (hints_cons _ _ _ (inp_5166 v h) (by intro d hd; cases hd)))
def cl_20176 : CNF.NClause := [(34,false),(87,false),(3,true),(70,false),(75,true),(65,true),(85,false)]
theorem der_20176 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20176 :=
  CNF.rup_sound cl_20176 [cl_4364,cl_4380] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4364 v h) (hints_cons _ _ _ (inp_4380 v h) (by intro d hd; cases hd)))
def cl_20180 : CNF.NClause := [(58,false),(69,false),(27,true),(89,true),(76,false),(78,false),(85,false)]
theorem der_20180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20180 :=
  CNF.rup_sound cl_20180 [cl_7492,cl_7490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7492 v h) (hints_cons _ _ _ (inp_7490 v h) (by intro d hd; cases hd)))
def cl_20185 : CNF.NClause := [(52,false),(88,false),(21,true),(66,false),(67,false),(85,false)]
theorem der_20185 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20185 :=
  CNF.rup_sound cl_20185 [cl_20005,cl_19995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20005 v h) (hints_cons _ _ _ (der_19995 v h) (by intro d hd; cases hd)))
def cl_20200 : CNF.NClause := [(57,false),(79,false),(26,true),(71,false),(75,true),(83,true),(91,false)]
theorem der_20200 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20200 :=
  CNF.rup_sound cl_20200 [cl_7340,cl_18657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7340 v h) (hints_cons _ _ _ (der_18657 v h) (by intro d hd; cases hd)))
def cl_20216 : CNF.NClause := [(102,true),(50,false),(38,true),(57,true),(32,false),(51,true)]
theorem der_20216 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20216 :=
  CNF.rup_sound cl_20216 [cl_2615,cl_2611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2615 v h) (hints_cons _ _ _ (inp_2611 v h) (by intro d hd; cases hd)))
def cl_20217 : CNF.NClause := [(97,true),(32,false),(37,true),(56,true),(42,false),(52,true)]
theorem der_20217 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20217 :=
  CNF.rup_sound cl_20217 [cl_2291,cl_18776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2291 v h) (hints_cons _ _ _ (der_18776 v h) (by intro d hd; cases hd)))
def cl_20224 : CNF.NClause := [(88,true),(0,true),(92,false),(31,false),(89,false),(90,false),(91,false)]
theorem der_20224 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20224 :=
  CNF.rup_sound cl_20224 [cl_3976,cl_3974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3976 v h) (hints_cons _ _ _ (inp_3974 v h) (by intro d hd; cases hd)))
def cl_20225 : CNF.NClause := [(0,true),(89,false),(91,false),(90,false),(31,false),(92,false)]
theorem der_20225 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20225 :=
  CNF.rup_sound cl_20225 [cl_14845,cl_20224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14845 v h) (hints_cons _ _ _ (der_20224 v h) (by intro d hd; cases hd)))
def cl_20239 : CNF.NClause := [(90,true),(8,true),(19,false),(11,false),(28,true),(22,false)]
theorem der_20239 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20239 :=
  CNF.rup_sound cl_20239 [cl_1828,cl_1827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1828 v h) (hints_cons _ _ _ (inp_1827 v h) (by intro d hd; cases hd)))
def cl_20240 : CNF.NClause := [(117,true),(45,false),(32,false),(53,true),(36,true)]
theorem der_20240 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20240 :=
  CNF.rup_sound cl_20240 [cl_18288,cl_18757] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18288 v h) (hints_cons _ _ _ (der_18757 v h) (by intro d hd; cases hd)))
def cl_20241 : CNF.NClause := [(52,false),(79,false),(88,false),(85,true),(66,false),(67,false),(21,true)]
theorem der_20241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20241 :=
  CNF.rup_sound cl_20241 [cl_18863,cl_6698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18863 v h) (hints_cons _ _ _ (inp_6698 v h) (by intro d hd; cases hd)))
def cl_20243 : CNF.NClause := [(65,true),(13,false),(3,true),(23,false),(8,true)]
theorem der_20243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20243 :=
  CNF.rup_sound cl_20243 [cl_18506,cl_18267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18506 v h) (hints_cons _ _ _ (der_18267 v h) (by intro d hd; cases hd)))
def cl_20245 : CNF.NClause := [(25,true),(63,true),(14,false),(24,false),(19,false),(9,true)]
theorem der_20245 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20245 :=
  CNF.rup_sound cl_20245 [cl_100,cl_19622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_100 v h) (hints_cons _ _ _ (der_19622 v h) (by intro d hd; cases hd)))
def cl_20246 : CNF.NClause := [(63,true),(14,false),(24,false),(19,false),(9,true)]
theorem der_20246 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20246 :=
  CNF.rup_sound cl_20246 [cl_19927,cl_20245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19927 v h) (hints_cons _ _ _ (der_20245 v h) (by intro d hd; cases hd)))
def cl_20251 : CNF.NClause := [(407,false),(12,true),(68,true),(9,true),(8,true),(16,true)]
theorem der_20251 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20251 :=
  CNF.rup_sound cl_20251 [cl_14047,cl_14051,cl_14044,cl_14040,cl_19656,cl_14064,cl_431,cl_9683,cl_14055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14047 v h) (hints_cons _ _ _ (inp_14051 v h) (hints_cons _ _ _ (inp_14044 v h) (hints_cons _ _ _ (inp_14040 v h) (hints_cons _ _ _ (der_19656 v h) (hints_cons _ _ _ (inp_14064 v h) (hints_cons _ _ _ (inp_431 v h) (hints_cons _ _ _ (inp_9683 v h) (hints_cons _ _ _ (inp_14055 v h) (by intro d hd; cases hd))))))))))
def cl_20252 : CNF.NClause := [(423,false),(12,true),(68,true),(9,true),(8,true),(16,true)]
theorem der_20252 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20252 :=
  CNF.rup_sound cl_20252 [cl_20251,cl_14047,cl_14051,cl_14044,cl_14055,cl_9679,cl_14064,cl_19655,cl_400] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20251 v h) (hints_cons _ _ _ (inp_14047 v h) (hints_cons _ _ _ (inp_14051 v h) (hints_cons _ _ _ (inp_14044 v h) (hints_cons _ _ _ (inp_14055 v h) (hints_cons _ _ _ (inp_9679 v h) (hints_cons _ _ _ (inp_14064 v h) (hints_cons _ _ _ (der_19655 v h) (hints_cons _ _ _ (inp_400 v h) (by intro d hd; cases hd))))))))))
def cl_20255 : CNF.NClause := [(118,true),(31,false),(32,false),(34,true),(61,true)]
theorem der_20255 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20255 :=
  CNF.rup_sound cl_20255 [cl_19825,cl_19999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19825 v h) (hints_cons _ _ _ (der_19999 v h) (by intro d hd; cases hd)))
def cl_20262 : CNF.NClause := [(4,false),(20,false),(12,true),(68,true),(8,true),(16,true)]
theorem der_20262 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20262 :=
  CNF.rup_sound cl_20262 [cl_19656,cl_431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19656 v h) (hints_cons _ _ _ (inp_431 v h) (by intro d hd; cases hd)))
def cl_20264 : CNF.NClause := [(71,true),(360,true),(19,false),(26,true),(7,true)]
theorem der_20264 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20264 :=
  CNF.rup_sound cl_20264 [cl_14001,cl_13742,cl_19763,cl_19891,cl_13977,cl_13988,cl_616,cl_9328,cl_13995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14001 v h) (hints_cons _ _ _ (inp_13742 v h) (hints_cons _ _ _ (der_19763 v h) (hints_cons _ _ _ (der_19891 v h) (hints_cons _ _ _ (inp_13977 v h) (hints_cons _ _ _ (inp_13988 v h) (hints_cons _ _ _ (inp_616 v h) (hints_cons _ _ _ (inp_9328 v h) (hints_cons _ _ _ (inp_13995 v h) (by intro d hd; cases hd))))))))))
def cl_20267 : CNF.NClause := [(94,true),(40,true),(55,false),(50,true),(45,false)]
theorem der_20267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20267 :=
  CNF.rup_sound cl_20267 [cl_19973,cl_19134,cl_2092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19973 v h) (hints_cons _ _ _ (der_19134 v h) (hints_cons _ _ _ (inp_2092 v h) (by intro d hd; cases hd))))
def cl_20269 : CNF.NClause := [(101,true),(51,false),(59,true),(37,true),(48,false),(45,false)]
theorem der_20269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20269 :=
  CNF.rup_sound cl_20269 [cl_2531,cl_2532] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2531 v h) (hints_cons _ _ _ (inp_2532 v h) (by intro d hd; cases hd)))
def cl_20270 : CNF.NClause := [(101,true),(59,true),(45,false),(37,true),(48,false)]
theorem der_20270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20270 :=
  CNF.rup_sound cl_20270 [cl_19945,cl_20269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19945 v h) (hints_cons _ _ _ (der_20269 v h) (by intro d hd; cases hd)))
def cl_20271 : CNF.NClause := [(110,true),(46,false),(57,true),(33,false),(52,true),(45,false)]
theorem der_20271 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20271 :=
  CNF.rup_sound cl_20271 [cl_3121,cl_17957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3121 v h) (hints_cons _ _ _ (der_17957 v h) (by intro d hd; cases hd)))
def cl_20272 : CNF.NClause := [(103,true),(43,true),(61,true),(45,false),(41,true),(42,false)]
theorem der_20272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20272 :=
  CNF.rup_sound cl_20272 [cl_2670,cl_2662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2670 v h) (hints_cons _ _ _ (inp_2662 v h) (by intro d hd; cases hd)))
def cl_20274 : CNF.NClause := [(81,false),(32,true),(87,false),(23,true),(76,false),(71,false),(12,true),(66,false),(86,false),(9,true),(28,true)]
theorem der_20274 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20274 :=
  CNF.rup_sound cl_20274 [cl_20136,cl_4097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20136 v h) (hints_cons _ _ _ (inp_4097 v h) (by intro d hd; cases hd)))
def cl_20275 : CNF.NClause := [(51,false),(69,false),(68,true),(71,false),(67,false),(92,false),(70,false)]
theorem der_20275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20275 :=
  CNF.rup_sound cl_20275 [cl_6533,cl_6534] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6533 v h) (hints_cons _ _ _ (inp_6534 v h) (by intro d hd; cases hd)))
def cl_20276 : CNF.NClause := [(438,false),(454,true),(446,true),(68,true),(8,true),(16,true),(10,true)]
theorem der_20276 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20276 :=
  CNF.rup_sound cl_20276 [cl_14074,cl_14081,cl_14070,cl_9869,cl_19656,cl_14094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14074 v h) (hints_cons _ _ _ (inp_14081 v h) (hints_cons _ _ _ (inp_14070 v h) (hints_cons _ _ _ (inp_9869 v h) (hints_cons _ _ _ (der_19656 v h) (hints_cons _ _ _ (inp_14094 v h) (by intro d hd; cases hd)))))))
def cl_20278 : CNF.NClause := [(59,false),(101,true),(37,true),(45,false),(51,true),(48,false)]
theorem der_20278 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20278 :=
  CNF.rup_sound cl_20278 [cl_2516,cl_2515] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2516 v h) (hints_cons _ _ _ (inp_2515 v h) (by intro d hd; cases hd)))
def cl_20279 : CNF.NClause := [(101,true),(45,false),(48,false),(51,true),(37,true)]
theorem der_20279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20279 :=
  CNF.rup_sound cl_20279 [cl_20270,cl_20278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20270 v h) (hints_cons _ _ _ (der_20278 v h) (by intro d hd; cases hd)))
def cl_20280 : CNF.NClause := [(110,true),(46,true),(57,true),(33,false),(45,false),(52,true)]
theorem der_20280 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20280 :=
  CNF.rup_sound cl_20280 [cl_3129,cl_3131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3129 v h) (hints_cons _ _ _ (inp_3131 v h) (by intro d hd; cases hd)))
def cl_20281 : CNF.NClause := [(34,false),(87,false),(80,false),(85,true),(70,false),(3,true),(75,true)]
theorem der_20281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20281 :=
  CNF.rup_sound cl_20281 [cl_19590,cl_4396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19590 v h) (hints_cons _ _ _ (inp_4396 v h) (by intro d hd; cases hd)))
def cl_20282 : CNF.NClause := [(73,true),(59,false),(28,true),(70,false),(84,false),(90,false),(81,true)]
theorem der_20282 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20282 :=
  CNF.rup_sound cl_20282 [cl_7578,cl_7580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7578 v h) (hints_cons _ _ _ (inp_7580 v h) (by intro d hd; cases hd)))
def cl_20283 : CNF.NClause := [(73,false),(59,false),(28,true),(70,false),(90,false),(81,true),(84,false)]
theorem der_20283 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20283 :=
  CNF.rup_sound cl_20283 [cl_7572,cl_7570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7572 v h) (hints_cons _ _ _ (inp_7570 v h) (by intro d hd; cases hd)))
def cl_20284 : CNF.NClause := [(59,false),(81,true),(28,true),(70,false),(84,false),(90,false)]
theorem der_20284 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20284 :=
  CNF.rup_sound cl_20284 [cl_20282,cl_20283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20282 v h) (hints_cons _ _ _ (der_20283 v h) (by intro d hd; cases hd)))
def cl_20286 : CNF.NClause := [(65,true),(294,true),(387,true),(384,true),(394,true),(285,false),(301,true),(398,true),(307,true),(306,true),(286,true),(300,true),(289,true),(381,true),(5,true),(402,true),(400,true),(399,true),(388,true),(393,true),(379,true),(8,true),(3,true)]
theorem der_20286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20286 :=
  CNF.rup_sound cl_20286 [cl_14009,cl_14011,cl_9596,cl_13743,cl_9578,cl_19376,cl_13933,cl_19168,cl_8969,cl_8998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14009 v h) (hints_cons _ _ _ (inp_14011 v h) (hints_cons _ _ _ (inp_9596 v h) (hints_cons _ _ _ (inp_13743 v h) (hints_cons _ _ _ (inp_9578 v h) (hints_cons _ _ _ (der_19376 v h) (hints_cons _ _ _ (inp_13933 v h) (hints_cons _ _ _ (der_19168 v h) (hints_cons _ _ _ (inp_8969 v h) (hints_cons _ _ _ (inp_8998 v h) (by intro d hd; cases hd)))))))))))
def cl_20287 : CNF.NClause := [(438,false),(12,true),(68,true),(8,true),(16,true),(10,true)]
theorem der_20287 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20287 :=
  CNF.rup_sound cl_20287 [cl_14077,cl_14070,cl_20276,cl_20262,cl_14085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14077 v h) (hints_cons _ _ _ (inp_14070 v h) (hints_cons _ _ _ (der_20276 v h) (hints_cons _ _ _ (der_20262 v h) (hints_cons _ _ _ (inp_14085 v h) (by intro d hd; cases hd))))))
def cl_20294 : CNF.NClause := [(80,true),(428,true),(423,true),(421,true),(415,true),(11,false),(429,true),(409,false),(413,true),(408,true),(9,true),(7,true),(3,true)]
theorem der_20294 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20294 :=
  CNF.rup_sound cl_20294 [cl_17683,cl_18352,cl_14059,cl_14050,cl_9820,cl_9827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17683 v h) (hints_cons _ _ _ (der_18352 v h) (hints_cons _ _ _ (inp_14059 v h) (hints_cons _ _ _ (inp_14050 v h) (hints_cons _ _ _ (inp_9820 v h) (hints_cons _ _ _ (inp_9827 v h) (by intro d hd; cases hd)))))))
def cl_20298 : CNF.NClause := [(14,false),(72,true),(11,false),(10,true),(30,true),(12,true)]
theorem der_20298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20298 :=
  CNF.rup_sound cl_20298 [cl_686,cl_678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_686 v h) (hints_cons _ _ _ (inp_678 v h) (by intro d hd; cases hd)))
def cl_20314 : CNF.NClause := [(123,true),(46,false),(31,false),(36,true),(41,true)]
theorem der_20314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20314 :=
  CNF.rup_sound cl_20314 [cl_19993,cl_19437,cl_3959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19993 v h) (hints_cons _ _ _ (der_19437 v h) (hints_cons _ _ _ (inp_3959 v h) (by intro d hd; cases hd))))
def cl_20315 : CNF.NClause := [(119,true),(44,false),(31,false),(52,true),(40,true)]
theorem der_20315 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20315 :=
  CNF.rup_sound cl_20315 [cl_19405,cl_18610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19405 v h) (hints_cons _ _ _ (der_18610 v h) (by intro d hd; cases hd)))
def cl_20316 : CNF.NClause := [(109,true),(44,false),(35,true),(37,true),(46,false),(53,true)]
theorem der_20316 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20316 :=
  CNF.rup_sound cl_20316 [cl_3028,cl_3060] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3028 v h) (hints_cons _ _ _ (inp_3060 v h) (by intro d hd; cases hd)))
def cl_20317 : CNF.NClause := [(108,true),(49,true),(46,false),(61,true),(50,false),(47,true)]
theorem der_20317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20317 :=
  CNF.rup_sound cl_20317 [cl_2987,cl_2991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2987 v h) (hints_cons _ _ _ (inp_2991 v h) (by intro d hd; cases hd)))
def cl_20320 : CNF.NClause := [(114,true),(57,true),(42,false),(36,true),(35,true),(54,false)]
theorem der_20320 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20320 :=
  CNF.rup_sound cl_20320 [cl_3364,cl_18369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3364 v h) (hints_cons _ _ _ (der_18369 v h) (by intro d hd; cases hd)))
def cl_20321 : CNF.NClause := [(95,true),(33,true),(38,true),(56,false),(43,false),(53,true)]
theorem der_20321 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20321 :=
  CNF.rup_sound cl_20321 [cl_2140,cl_2132] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2140 v h) (hints_cons _ _ _ (inp_2132 v h) (by intro d hd; cases hd)))
def cl_20323 : CNF.NClause := [(33,false),(84,true),(79,false),(87,false),(69,false),(64,false),(74,false)]
theorem der_20323 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20323 :=
  CNF.rup_sound cl_20323 [cl_19562,cl_4257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19562 v h) (hints_cons _ _ _ (inp_4257 v h) (by intro d hd; cases hd)))
def cl_20324 : CNF.NClause := [(112,true),(59,true),(46,false),(43,false),(40,true),(54,false)]
theorem der_20324 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20324 :=
  CNF.rup_sound cl_20324 [cl_3235,cl_3236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3235 v h) (hints_cons _ _ _ (inp_3236 v h) (by intro d hd; cases hd)))
def cl_20326 : CNF.NClause := [(97,true),(52,true),(37,true),(56,false),(42,false),(47,true)]
theorem der_20326 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20326 :=
  CNF.rup_sound cl_20326 [cl_2268,cl_18776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2268 v h) (hints_cons _ _ _ (der_18776 v h) (by intro d hd; cases hd)))
def cl_20334 : CNF.NClause := [(84,true),(788,false),(13,false),(5,true),(28,true),(16,true),(21,true)]
theorem der_20334 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20334 :=
  CNF.rup_sound cl_20334 [cl_14401,cl_14423,cl_14412,cl_19255,cl_19091,cl_14419,cl_14398,cl_12009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14401 v h) (hints_cons _ _ _ (inp_14423 v h) (hints_cons _ _ _ (inp_14412 v h) (hints_cons _ _ _ (der_19255 v h) (hints_cons _ _ _ (der_19091 v h) (hints_cons _ _ _ (inp_14419 v h) (hints_cons _ _ _ (inp_14398 v h) (hints_cons _ _ _ (inp_12009 v h) (by intro d hd; cases hd)))))))))
def cl_20345 : CNF.NClause := [(294,true),(308,false),(303,true),(279,true),(297,true),(296,true),(301,true),(287,true),(309,true),(307,true),(286,true),(295,true),(282,true)]
theorem der_20345 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20345 :=
  CNF.rup_sound cl_20345 [cl_8989,cl_9006,cl_9069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8989 v h) (hints_cons _ _ _ (inp_9006 v h) (hints_cons _ _ _ (inp_9069 v h) (by intro d hd; cases hd))))
def cl_20351 : CNF.NClause := [(52,false),(79,false),(73,true),(85,false),(66,false),(67,false),(21,true)]
theorem der_20351 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20351 :=
  CNF.rup_sound cl_20351 [cl_20185,cl_6730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20185 v h) (hints_cons _ _ _ (inp_6730 v h) (by intro d hd; cases hd)))
def cl_20352 : CNF.NClause := [(102,true),(50,false),(38,true),(57,true),(51,false),(32,false)]
theorem der_20352 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20352 :=
  CNF.rup_sound cl_20352 [cl_2599,cl_2595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2599 v h) (hints_cons _ _ _ (inp_2595 v h) (by intro d hd; cases hd)))
def cl_20369 : CNF.NClause := [(52,false),(88,true),(21,true),(66,false),(67,false),(73,true),(85,false)]
theorem der_20369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20369 :=
  CNF.rup_sound cl_20369 [cl_6746,cl_20351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6746 v h) (hints_cons _ _ _ (der_20351 v h) (by intro d hd; cases hd)))
def cl_20370 : CNF.NClause := [(52,false),(73,true),(85,false),(66,false),(67,false),(21,true)]
theorem der_20370 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20370 :=
  CNF.rup_sound cl_20370 [cl_20185,cl_20369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20185 v h) (hints_cons _ _ _ (der_20369 v h) (by intro d hd; cases hd)))
def cl_20371 : CNF.NClause := [(39,false),(76,true),(8,true),(90,false),(68,false),(65,false),(82,true)]
theorem der_20371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20371 :=
  CNF.rup_sound cl_20371 [cl_5034,cl_5050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5034 v h) (hints_cons _ _ _ (inp_5050 v h) (by intro d hd; cases hd)))
def cl_20381 : CNF.NClause := [(110,true),(45,false),(46,false),(57,true),(52,true),(39,true)]
theorem der_20381 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20381 :=
  CNF.rup_sound cl_20381 [cl_20271,cl_3124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20271 v h) (hints_cons _ _ _ (inp_3124 v h) (by intro d hd; cases hd)))
def cl_20382 : CNF.NClause := [(58,false),(89,false),(27,true),(76,true),(69,false),(78,false),(85,false)]
theorem der_20382 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20382 :=
  CNF.rup_sound cl_20382 [cl_7436,cl_7434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7436 v h) (hints_cons _ _ _ (inp_7434 v h) (by intro d hd; cases hd)))
def cl_20383 : CNF.NClause := [(112,true),(46,false),(40,true),(43,false),(32,true),(54,true)]
theorem der_20383 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20383 :=
  CNF.rup_sound cl_20383 [cl_3220,cl_3252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3220 v h) (hints_cons _ _ _ (inp_3252 v h) (by intro d hd; cases hd)))
def cl_20386 : CNF.NClause := [(63,true),(14,false),(4,false),(19,false),(9,true)]
theorem der_20386 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20386 :=
  CNF.rup_sound cl_20386 [cl_19927,cl_19622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19927 v h) (hints_cons _ _ _ (der_19622 v h) (by intro d hd; cases hd)))
def cl_20389 : CNF.NClause := [(52,false),(88,true),(21,true),(66,false),(73,false),(67,false),(85,false)]
theorem der_20389 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20389 :=
  CNF.rup_sound cl_20389 [cl_6738,cl_19758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6738 v h) (hints_cons _ _ _ (der_19758 v h) (by intro d hd; cases hd)))
def cl_20390 : CNF.NClause := [(52,false),(73,false),(85,false),(66,false),(67,false),(21,true)]
theorem der_20390 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20390 :=
  CNF.rup_sound cl_20390 [cl_20185,cl_20389] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20185 v h) (hints_cons _ _ _ (der_20389 v h) (by intro d hd; cases hd)))
def cl_20392 : CNF.NClause := [(121,true),(31,true),(39,true),(42,false),(50,false),(53,true)]
theorem der_20392 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20392 :=
  CNF.rup_sound cl_20392 [cl_3796,cl_3828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3796 v h) (hints_cons _ _ _ (inp_3828 v h) (by intro d hd; cases hd)))
def cl_20395 : CNF.NClause := [(58,false),(76,false),(27,true),(69,false),(85,false),(78,false)]
theorem der_20395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20395 :=
  CNF.rup_sound cl_20395 [cl_19944,cl_20180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19944 v h) (hints_cons _ _ _ (der_20180 v h) (by intro d hd; cases hd)))
def cl_20396 : CNF.NClause := [(122,true),(49,false),(43,false),(57,true),(37,true)]
theorem der_20396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20396 :=
  CNF.rup_sound cl_20396 [cl_20121,cl_19984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20121 v h) (hints_cons _ _ _ (der_19984 v h) (by intro d hd; cases hd)))
def cl_20399 : CNF.NClause := [(13,false),(88,false),(44,true),(71,false),(24,false),(65,false),(72,false),(5,true),(78,false),(28,true),(16,true)]
theorem der_20399 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20399 :=
  CNF.rup_sound cl_20399 [cl_19255,cl_5633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19255 v h) (hints_cons _ _ _ (inp_5633 v h) (by intro d hd; cases hd)))
def cl_20402 : CNF.NClause := [(65,true),(76,true),(8,true),(68,false),(90,false),(39,false),(82,true)]
theorem der_20402 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20402 :=
  CNF.rup_sound cl_20402 [cl_5036,cl_5052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5036 v h) (hints_cons _ _ _ (inp_5052 v h) (by intro d hd; cases hd)))
def cl_20403 : CNF.NClause := [(39,false),(76,true),(8,true),(90,false),(68,false),(82,true)]
theorem der_20403 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20403 :=
  CNF.rup_sound cl_20403 [cl_20371,cl_20402] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20371 v h) (hints_cons _ _ _ (der_20402 v h) (by intro d hd; cases hd)))
def cl_20404 : CNF.NClause := [(39,false),(90,false),(82,true),(8,true),(68,false)]
theorem der_20404 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20404 :=
  CNF.rup_sound cl_20404 [cl_20124,cl_20403] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20124 v h) (hints_cons _ _ _ (der_20403 v h) (by intro d hd; cases hd)))
def cl_20407 : CNF.NClause := [(87,true),(2,true),(438,false),(30,true),(3,true),(10,true)]
theorem der_20407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20407 :=
  CNF.rup_sound cl_20407 [cl_14068,cl_14070,cl_14095,cl_14069,cl_18560,cl_19557,cl_14067,cl_14066,cl_9979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14068 v h) (hints_cons _ _ _ (inp_14070 v h) (hints_cons _ _ _ (inp_14095 v h) (hints_cons _ _ _ (inp_14069 v h) (hints_cons _ _ _ (der_18560 v h) (hints_cons _ _ _ (der_19557 v h) (hints_cons _ _ _ (inp_14067 v h) (hints_cons _ _ _ (inp_14066 v h) (hints_cons _ _ _ (inp_9979 v h) (by intro d hd; cases hd))))))))))
def cl_20412 : CNF.NClause := [(92,false),(83,false),(5,true),(85,true),(86,false),(82,false),(36,false)]
theorem der_20412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20412 :=
  CNF.rup_sound cl_20412 [cl_4626,cl_4634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4626 v h) (hints_cons _ _ _ (inp_4634 v h) (by intro d hd; cases hd)))
def cl_20414 : CNF.NClause := [(83,true),(92,false),(5,true),(82,false),(86,false),(85,true),(36,false)]
theorem der_20414 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20414 :=
  CNF.rup_sound cl_20414 [cl_4630,cl_4638] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4630 v h) (hints_cons _ _ _ (inp_4638 v h) (by intro d hd; cases hd)))
def cl_20415 : CNF.NClause := [(92,false),(36,false),(5,true),(85,true),(86,false),(82,false)]
theorem der_20415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20415 :=
  CNF.rup_sound cl_20415 [cl_20412,cl_20414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20412 v h) (hints_cons _ _ _ (der_20414 v h) (by intro d hd; cases hd)))
def cl_20416 : CNF.NClause := [(83,true),(4,false),(5,true),(23,true),(26,false),(17,true)]
theorem der_20416 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20416 :=
  CNF.rup_sound cl_20416 [cl_1371,cl_1375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1371 v h) (hints_cons _ _ _ (inp_1375 v h) (by intro d hd; cases hd)))
def cl_20417 : CNF.NClause := [(83,false),(36,false),(5,true),(85,true),(92,true),(82,false),(86,false)]
theorem der_20417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20417 :=
  CNF.rup_sound cl_20417 [cl_4690,cl_4698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4690 v h) (hints_cons _ _ _ (inp_4698 v h) (by intro d hd; cases hd)))
def cl_20420 : CNF.NClause := [(489,true),(482,true),(494,true),(488,true),(476,false),(477,true),(492,true),(475,true),(474,true),(472,true),(493,true),(468,true),(473,true)]
theorem der_20420 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20420 :=
  CNF.rup_sound cl_20420 [cl_10125,cl_10103,cl_10130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_10125 v h) (hints_cons _ _ _ (inp_10103 v h) (hints_cons _ _ _ (inp_10130 v h) (by intro d hd; cases hd))))
def cl_20424 : CNF.NClause := [(425,true),(432,true),(405,true),(415,true),(420,true),(433,true),(431,true),(430,true),(419,true),(413,true),(410,true),(9,true),(3,true)]
theorem der_20424 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20424 :=
  CNF.rup_sound cl_20424 [cl_15194,cl_9654,cl_9646] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15194 v h) (hints_cons _ _ _ (inp_9654 v h) (hints_cons _ _ _ (inp_9646 v h) (by intro d hd; cases hd))))
def cl_20425 : CNF.NClause := [(90,true),(0,false),(28,true),(8,false),(19,true),(22,false)]
theorem der_20425 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20425 :=
  CNF.rup_sound cl_20425 [cl_1833,cl_1837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1833 v h) (hints_cons _ _ _ (inp_1837 v h) (by intro d hd; cases hd)))
def cl_20426 : CNF.NClause := [(0,true),(90,true),(8,false),(28,true),(19,true),(22,false)]
theorem der_20426 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20426 :=
  CNF.rup_sound cl_20426 [cl_1834,cl_1838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1834 v h) (hints_cons _ _ _ (inp_1838 v h) (by intro d hd; cases hd)))
def cl_20427 : CNF.NClause := [(90,true),(22,false),(28,true),(8,false),(19,true)]
theorem der_20427 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20427 :=
  CNF.rup_sound cl_20427 [cl_20425,cl_20426] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20425 v h) (hints_cons _ _ _ (der_20426 v h) (by intro d hd; cases hd)))
def cl_20429 : CNF.NClause := [(15,false),(13,false),(78,true),(6,true),(27,true),(22,false)]
theorem der_20429 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20429 :=
  CNF.rup_sound cl_20429 [cl_1060,cl_1059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1060 v h) (hints_cons _ _ _ (inp_1059 v h) (by intro d hd; cases hd)))
def cl_20431 : CNF.NClause := [(13,true),(15,false),(6,true),(78,true),(27,true),(22,false)]
theorem der_20431 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20431 :=
  CNF.rup_sound cl_20431 [cl_1063,cl_1064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1063 v h) (hints_cons _ _ _ (inp_1064 v h) (by intro d hd; cases hd)))
def cl_20432 : CNF.NClause := [(15,false),(78,true),(22,false),(6,true),(27,true)]
theorem der_20432 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20432 :=
  CNF.rup_sound cl_20432 [cl_20429,cl_20431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20429 v h) (hints_cons _ _ _ (der_20431 v h) (by intro d hd; cases hd)))
def cl_20433 : CNF.NClause := [(4,false),(6,true),(27,true),(78,true),(15,true),(22,false)]
theorem der_20433 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20433 :=
  CNF.rup_sound cl_20433 [cl_1067,cl_1071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1067 v h) (hints_cons _ _ _ (inp_1071 v h) (by intro d hd; cases hd)))
def cl_20439 : CNF.NClause := [(29,true),(453,true),(23,true),(19,false),(74,true),(10,true)]
theorem der_20439 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20439 :=
  CNF.rup_sound cl_20439 [cl_14088,cl_19906,cl_14072,cl_13745,cl_14094,cl_823,cl_9903,cl_14068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14088 v h) (hints_cons _ _ _ (der_19906 v h) (hints_cons _ _ _ (inp_14072 v h) (hints_cons _ _ _ (inp_13745 v h) (hints_cons _ _ _ (inp_14094 v h) (hints_cons _ _ _ (inp_823 v h) (hints_cons _ _ _ (inp_9903 v h) (hints_cons _ _ _ (inp_14068 v h) (by intro d hd; cases hd)))))))))
def cl_20440 : CNF.NClause := [(29,false),(23,true),(6,true),(74,true),(10,true),(19,false)]
theorem der_20440 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20440 :=
  CNF.rup_sound cl_20440 [cl_792,cl_791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_792 v h) (hints_cons _ _ _ (inp_791 v h) (by intro d hd; cases hd)))
def cl_20442 : CNF.NClause := [(11,false),(90,true),(22,false),(8,false),(28,true),(19,false)]
theorem der_20442 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20442 :=
  CNF.rup_sound cl_20442 [cl_1825,cl_1826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1825 v h) (hints_cons _ _ _ (inp_1826 v h) (by intro d hd; cases hd)))
def cl_20443 : CNF.NClause := [(11,true),(90,true),(8,false),(28,true),(19,false),(22,false)]
theorem der_20443 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20443 :=
  CNF.rup_sound cl_20443 [cl_1829,cl_1830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1829 v h) (hints_cons _ _ _ (inp_1830 v h) (by intro d hd; cases hd)))
def cl_20444 : CNF.NClause := [(90,true),(19,false),(22,false),(8,false),(28,true)]
theorem der_20444 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20444 :=
  CNF.rup_sound cl_20444 [cl_20442,cl_20443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20442 v h) (hints_cons _ _ _ (der_20443 v h) (by intro d hd; cases hd)))
def cl_20446 : CNF.NClause := [(29,false),(19,false),(6,true),(74,true),(10,true)]
theorem der_20446 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20446 :=
  CNF.rup_sound cl_20446 [cl_20440,cl_15412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20440 v h) (hints_cons _ _ _ (der_15412 v h) (by intro d hd; cases hd)))
def cl_20447 : CNF.NClause := [(23,false),(6,true),(74,true),(29,true),(10,true),(19,false)]
theorem der_20447 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20447 :=
  CNF.rup_sound cl_20447 [cl_808,cl_807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_808 v h) (hints_cons _ _ _ (inp_807 v h) (by intro d hd; cases hd)))
def cl_20449 : CNF.NClause := [(24,true),(15,true),(3,true),(7,true),(80,false),(29,true)]
theorem der_20449 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20449 :=
  CNF.rup_sound cl_20449 [cl_1216,cl_1212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1216 v h) (hints_cons _ _ _ (inp_1212 v h) (by intro d hd; cases hd)))
def cl_20452 : CNF.NClause := [(23,true),(664,false),(670,true),(67,true),(657,true),(24,false),(680,true),(22,true),(679,true),(656,true),(661,true),(667,true),(17,true),(21,true),(30,true)]
theorem der_20452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20452 :=
  CNF.rup_sound cl_20452 [cl_14297,cl_14305,cl_14296,cl_367,cl_14298,cl_14295,cl_11207,cl_11161,cl_11265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14297 v h) (hints_cons _ _ _ (inp_14305 v h) (hints_cons _ _ _ (inp_14296 v h) (hints_cons _ _ _ (inp_367 v h) (hints_cons _ _ _ (inp_14298 v h) (hints_cons _ _ _ (inp_14295 v h) (hints_cons _ _ _ (inp_11207 v h) (hints_cons _ _ _ (inp_11161 v h) (hints_cons _ _ _ (inp_11265 v h) (by intro d hd; cases hd))))))))))
def cl_20453 : CNF.NClause := [(23,false),(67,true),(30,true),(21,true),(22,true),(24,false)]
theorem der_20453 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20453 :=
  CNF.rup_sound cl_20453 [cl_359,cl_360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_359 v h) (hints_cons _ _ _ (inp_360 v h) (by intro d hd; cases hd)))
def cl_20454 : CNF.NClause := [(664,false),(670,true),(30,true),(67,true),(657,true),(24,false),(680,true),(22,true),(679,true),(656,true),(661,true),(667,true),(17,true),(21,true)]
theorem der_20454 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20454 :=
  CNF.rup_sound cl_20454 [cl_20452,cl_20453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20452 v h) (hints_cons _ _ _ (der_20453 v h) (by intro d hd; cases hd)))
def cl_20456 : CNF.NClause := [(65,false),(77,true),(86,false),(49,false),(18,false),(73,false),(91,false)]
theorem der_20456 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20456 :=
  CNF.rup_sound cl_20456 [cl_6289,cl_6293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6289 v h) (hints_cons _ _ _ (inp_6293 v h) (by intro d hd; cases hd)))
def cl_20457 : CNF.NClause := [(65,true),(91,false),(18,false),(49,false),(73,false),(77,true),(86,false)]
theorem der_20457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20457 :=
  CNF.rup_sound cl_20457 [cl_6295,cl_6291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6295 v h) (hints_cons _ _ _ (inp_6291 v h) (by intro d hd; cases hd)))
def cl_20458 : CNF.NClause := [(77,true),(91,false),(86,false),(49,false),(18,false),(73,false)]
theorem der_20458 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20458 :=
  CNF.rup_sound cl_20458 [cl_20456,cl_20457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20456 v h) (hints_cons _ _ _ (der_20457 v h) (by intro d hd; cases hd)))
def cl_20462 : CNF.NClause := [(670,false),(6,true),(29,true),(17,true),(74,true),(10,true)]
theorem der_20462 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20462 :=
  CNF.rup_sound cl_20462 [cl_14282,cl_14304,cl_14286,cl_14294,cl_20447,cl_14298,cl_823,cl_11204,cl_14278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14282 v h) (hints_cons _ _ _ (inp_14304 v h) (hints_cons _ _ _ (inp_14286 v h) (hints_cons _ _ _ (inp_14294 v h) (hints_cons _ _ _ (der_20447 v h) (hints_cons _ _ _ (inp_14298 v h) (hints_cons _ _ _ (inp_823 v h) (hints_cons _ _ _ (inp_11204 v h) (hints_cons _ _ _ (inp_14278 v h) (by intro d hd; cases hd))))))))))
def cl_20463 : CNF.NClause := [(90,true),(19,false),(28,true),(8,false),(11,false),(22,true)]
theorem der_20463 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20463 :=
  CNF.rup_sound cl_20463 [cl_1841,cl_1842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1841 v h) (hints_cons _ _ _ (inp_1842 v h) (by intro d hd; cases hd)))
def cl_20466 : CNF.NClause := [(6,false),(19,true),(29,false),(74,true),(10,true)]
theorem der_20466 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20466 :=
  CNF.rup_sound cl_20466 [cl_18474,cl_18789,cl_798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18474 v h) (hints_cons _ _ _ (der_18789 v h) (hints_cons _ _ _ (inp_798 v h) (by intro d hd; cases hd))))
def cl_20467 : CNF.NClause := [(6,true),(24,true),(18,false),(12,false),(26,false),(91,true)]
theorem der_20467 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20467 :=
  CNF.rup_sound cl_20467 [cl_1876,cl_1875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1876 v h) (hints_cons _ _ _ (inp_1875 v h) (by intro d hd; cases hd)))
def cl_20472 : CNF.NClause := [(23,false),(19,true),(29,false),(74,true),(10,true),(6,true)]
theorem der_20472 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20472 :=
  CNF.rup_sound cl_20472 [cl_784,cl_783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_784 v h) (hints_cons _ _ _ (inp_783 v h) (by intro d hd; cases hd)))
def cl_20478 : CNF.NClause := [(81,true),(12,false),(15,false),(9,false),(28,true),(23,true)]
theorem der_20478 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20478 :=
  CNF.rup_sound cl_20478 [cl_1266,cl_1265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1266 v h) (hints_cons _ _ _ (inp_1265 v h) (by intro d hd; cases hd)))
def cl_20484 : CNF.NClause := [(11,true),(90,true),(783,false),(19,true),(22,true),(8,false),(21,true),(28,true)]
theorem der_20484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20484 :=
  CNF.rup_sound cl_20484 [cl_14415,cl_14417,cl_14423,cl_14407,cl_1853,cl_12046,cl_14396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14415 v h) (hints_cons _ _ _ (inp_14417 v h) (hints_cons _ _ _ (inp_14423 v h) (hints_cons _ _ _ (inp_14407 v h) (hints_cons _ _ _ (inp_1853 v h) (hints_cons _ _ _ (inp_12046 v h) (hints_cons _ _ _ (inp_14396 v h) (by intro d hd; cases hd))))))))
def cl_20485 : CNF.NClause := [(11,false),(90,true),(19,true),(8,false),(28,true),(22,true)]
theorem der_20485 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20485 :=
  CNF.rup_sound cl_20485 [cl_1849,cl_1850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1849 v h) (hints_cons _ _ _ (inp_1850 v h) (by intro d hd; cases hd)))
def cl_20486 : CNF.NClause := [(90,true),(783,false),(28,true),(19,true),(22,true),(8,false),(21,true)]
theorem der_20486 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20486 :=
  CNF.rup_sound cl_20486 [cl_20484,cl_20485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20484 v h) (hints_cons _ _ _ (der_20485 v h) (by intro d hd; cases hd)))
def cl_20488 : CNF.NClause := [(65,false),(91,false),(18,true),(73,true),(77,true),(49,false),(86,false)]
theorem der_20488 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20488 :=
  CNF.rup_sound cl_20488 [cl_6298,cl_6302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6298 v h) (hints_cons _ _ _ (inp_6302 v h) (by intro d hd; cases hd)))
def cl_20492 : CNF.NClause := [(91,true),(24,true),(26,false),(6,false),(12,false),(18,false)]
theorem der_20492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20492 :=
  CNF.rup_sound cl_20492 [cl_1873,cl_1874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1873 v h) (hints_cons _ _ _ (inp_1874 v h) (by intro d hd; cases hd)))
def cl_20493 : CNF.NClause := [(91,true),(18,false),(12,false),(6,false),(26,false)]
theorem der_20493 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20493 :=
  CNF.rup_sound cl_20493 [cl_15077,cl_20492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15077 v h) (hints_cons _ _ _ (der_20492 v h) (by intro d hd; cases hd)))
def cl_20499 : CNF.NClause := [(71,true),(20,false),(19,true),(13,false),(7,true),(26,false)]
theorem der_20499 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20499 :=
  CNF.rup_sound cl_20499 [cl_588,cl_587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_588 v h) (hints_cons _ _ _ (inp_587 v h) (by intro d hd; cases hd)))
def cl_20502 : CNF.NClause := [(65,true),(25,false),(3,true),(8,false),(18,false),(23,true)]
theorem der_20502 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20502 :=
  CNF.rup_sound cl_20502 [cl_214,cl_210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_214 v h) (hints_cons _ _ _ (inp_210 v h) (by intro d hd; cases hd)))
def cl_20506 : CNF.NClause := [(121,true),(59,true),(50,true),(39,false),(31,false),(53,true)]
theorem der_20506 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20506 :=
  CNF.rup_sound cl_20506 [cl_3833,cl_3837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3833 v h) (hints_cons _ _ _ (inp_3837 v h) (by intro d hd; cases hd)))
def cl_20510 : CNF.NClause := [(91,true),(18,false),(12,false),(6,true),(26,false)]
theorem der_20510 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20510 :=
  CNF.rup_sound cl_20510 [cl_15077,cl_20467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15077 v h) (hints_cons _ _ _ (der_20467 v h) (by intro d hd; cases hd)))
def cl_20512 : CNF.NClause := [(20,true),(71,true),(26,false),(13,false),(7,true),(19,true)]
theorem der_20512 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20512 :=
  CNF.rup_sound cl_20512 [cl_604,cl_603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_604 v h) (hints_cons _ _ _ (inp_603 v h) (by intro d hd; cases hd)))
def cl_20513 : CNF.NClause := [(71,true),(13,false),(19,true),(26,false),(7,true)]
theorem der_20513 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20513 :=
  CNF.rup_sound cl_20513 [cl_20499,cl_20512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20499 v h) (hints_cons _ _ _ (der_20512 v h) (by intro d hd; cases hd)))
def cl_20514 : CNF.NClause := [(91,true),(18,true),(49,false),(77,true),(73,true),(65,false),(86,false)]
theorem der_20514 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20514 :=
  CNF.rup_sound cl_20514 [cl_6362,cl_6366] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6362 v h) (hints_cons _ _ _ (inp_6366 v h) (by intro d hd; cases hd)))
def cl_20515 : CNF.NClause := [(65,false),(18,true),(86,false),(73,true),(77,true),(49,false)]
theorem der_20515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20515 :=
  CNF.rup_sound cl_20515 [cl_20488,cl_20514] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20488 v h) (hints_cons _ _ _ (der_20514 v h) (by intro d hd; cases hd)))
def cl_20520 : CNF.NClause := [(66,true),(1,false),(25,false),(6,true),(16,true),(21,true)]
theorem der_20520 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20520 :=
  CNF.rup_sound cl_20520 [cl_283,cl_287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_283 v h) (hints_cons _ _ _ (inp_287 v h) (by intro d hd; cases hd)))
def cl_20524 : CNF.NClause := [(50,false),(77,false),(90,false),(71,false),(74,true),(19,true),(85,true)]
theorem der_20524 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20524 :=
  CNF.rup_sound cl_20524 [cl_6442,cl_6444] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6442 v h) (hints_cons _ _ _ (inp_6444 v h) (by intro d hd; cases hd)))
def cl_20525 : CNF.NClause := [(59,false),(84,false),(28,true),(73,false),(62,false),(81,false),(90,false)]
theorem der_20525 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20525 :=
  CNF.rup_sound cl_20525 [cl_7558,cl_19328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7558 v h) (hints_cons _ _ _ (der_19328 v h) (by intro d hd; cases hd)))
def cl_20530 : CNF.NClause := [(79,true),(2,true),(8,false),(15,false),(26,false),(21,true)]
theorem der_20530 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20530 :=
  CNF.rup_sound cl_20530 [cl_1106,cl_1110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1106 v h) (hints_cons _ _ _ (inp_1110 v h) (by intro d hd; cases hd)))
def cl_20536 : CNF.NClause := [(87,true),(460,true),(459,true),(457,false),(440,true),(451,true),(2,true),(439,true),(455,true),(450,true),(10,true),(3,true),(30,true)]
theorem der_20536 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20536 :=
  CNF.rup_sound cl_20536 [cl_14068,cl_14069,cl_14095,cl_20407,cl_9955,cl_9855,cl_14067,cl_9982,cl_18779,cl_1661,cl_14066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14068 v h) (hints_cons _ _ _ (inp_14069 v h) (hints_cons _ _ _ (inp_14095 v h) (hints_cons _ _ _ (der_20407 v h) (hints_cons _ _ _ (inp_9955 v h) (hints_cons _ _ _ (inp_9855 v h) (hints_cons _ _ _ (inp_14067 v h) (hints_cons _ _ _ (inp_9982 v h) (hints_cons _ _ _ (der_18779 v h) (hints_cons _ _ _ (inp_1661 v h) (hints_cons _ _ _ (inp_14066 v h) (by intro d hd; cases hd))))))))))))
def cl_20537 : CNF.NClause := [(1,false),(76,true),(27,true),(10,true),(8,false),(17,true)]
theorem der_20537 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20537 :=
  CNF.rup_sound cl_20537 [cl_941,cl_957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_941 v h) (hints_cons _ _ _ (inp_957 v h) (by intro d hd; cases hd)))
def cl_20538 : CNF.NClause := [(76,true),(783,false),(10,true),(17,true),(27,true),(8,false),(21,true)]
theorem der_20538 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20538 :=
  CNF.rup_sound cl_20538 [cl_14406,cl_14413,cl_14422,cl_20537,cl_14397,cl_942,cl_11962,cl_14419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14406 v h) (hints_cons _ _ _ (inp_14413 v h) (hints_cons _ _ _ (inp_14422 v h) (hints_cons _ _ _ (der_20537 v h) (hints_cons _ _ _ (inp_14397 v h) (hints_cons _ _ _ (inp_942 v h) (hints_cons _ _ _ (inp_11962 v h) (hints_cons _ _ _ (inp_14419 v h) (by intro d hd; cases hd)))))))))
def cl_20540 : CNF.NClause := [(4,false),(68,true),(16,true),(8,false),(29,true),(12,false)]
theorem der_20540 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20540 :=
  CNF.rup_sound cl_20540 [cl_441,cl_425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_441 v h) (hints_cons _ _ _ (inp_425 v h) (by intro d hd; cases hd)))
def cl_20541 : CNF.NClause := [(4,true),(68,true),(8,false),(12,false),(16,true),(29,true)]
theorem der_20541 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20541 :=
  CNF.rup_sound cl_20541 [cl_426,cl_442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_426 v h) (hints_cons _ _ _ (inp_442 v h) (by intro d hd; cases hd)))
def cl_20542 : CNF.NClause := [(68,true),(12,false),(16,true),(8,false),(29,true)]
theorem der_20542 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20542 :=
  CNF.rup_sound cl_20542 [cl_20540,cl_20541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20540 v h) (hints_cons _ _ _ (der_20541 v h) (by intro d hd; cases hd)))
def cl_20545 : CNF.NClause := [(9,false),(75,true),(3,true),(16,true),(10,true),(26,false)]
theorem der_20545 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20545 :=
  CNF.rup_sound cl_20545 [cl_846,cl_862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_846 v h) (hints_cons _ _ _ (inp_862 v h) (by intro d hd; cases hd)))
def cl_20548 : CNF.NClause := [(6,true),(10,false),(29,true),(74,true),(19,true),(23,false)]
theorem der_20548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20548 :=
  CNF.rup_sound cl_20548 [cl_811,cl_812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_811 v h) (hints_cons _ _ _ (inp_812 v h) (by intro d hd; cases hd)))
def cl_20549 : CNF.NClause := [(6,false),(10,false),(74,true),(29,true),(19,true),(23,false)]
theorem der_20549 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20549 :=
  CNF.rup_sound cl_20549 [cl_810,cl_809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_810 v h) (hints_cons _ _ _ (inp_809 v h) (by intro d hd; cases hd)))
def cl_20550 : CNF.NClause := [(10,false),(74,true),(29,true),(23,false),(19,true)]
theorem der_20550 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20550 :=
  CNF.rup_sound cl_20550 [cl_20548,cl_20549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20548 v h) (hints_cons _ _ _ (der_20549 v h) (by intro d hd; cases hd)))
def cl_20552 : CNF.NClause := [(67,false),(64,false),(22,true),(86,false),(90,false),(75,false),(53,false)]
theorem der_20552 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20552 :=
  CNF.rup_sound cl_20552 [cl_6786,cl_6802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6786 v h) (hints_cons _ _ _ (inp_6802 v h) (by intro d hd; cases hd)))
def cl_20553 : CNF.NClause := [(67,true),(64,false),(22,true),(90,false),(75,false),(53,false),(86,false)]
theorem der_20553 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20553 :=
  CNF.rup_sound cl_20553 [cl_6790,cl_6806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6790 v h) (hints_cons _ _ _ (inp_6806 v h) (by intro d hd; cases hd)))
def cl_20554 : CNF.NClause := [(64,false),(22,true),(53,false),(86,false),(90,false),(75,false)]
theorem der_20554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20554 :=
  CNF.rup_sound cl_20554 [cl_20552,cl_20553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20552 v h) (hints_cons _ _ _ (der_20553 v h) (by intro d hd; cases hd)))
def cl_20556 : CNF.NClause := [(458,true),(435,true),(460,true),(456,true),(457,false),(436,true),(453,true),(439,true),(455,true),(450,true),(462,true),(464,true),(441,true)]
theorem der_20556 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20556 :=
  CNF.rup_sound cl_20556 [cl_9963,cl_9860,cl_9883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_9963 v h) (hints_cons _ _ _ (inp_9860 v h) (hints_cons _ _ _ (inp_9883 v h) (by intro d hd; cases hd))))
def cl_20586 : CNF.NClause := [(69,false),(73,true),(18,false),(49,false),(86,false),(77,false),(91,false)]
theorem der_20586 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20586 :=
  CNF.rup_sound cl_20586 [cl_6281,cl_6283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6281 v h) (hints_cons _ _ _ (inp_6283 v h) (by intro d hd; cases hd)))
def cl_20588 : CNF.NClause := [(69,true),(11,false),(2,true),(9,false),(27,true),(18,false)]
theorem der_20588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20588 :=
  CNF.rup_sound cl_20588 [cl_482,cl_498] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_482 v h) (hints_cons _ _ _ (inp_498 v h) (by intro d hd; cases hd)))
def cl_20610 : CNF.NClause := [(69,true),(18,false),(2,true),(9,false),(27,true),(11,true)]
theorem der_20610 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20610 :=
  CNF.rup_sound cl_20610 [cl_502,cl_486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_502 v h) (hints_cons _ _ _ (inp_486 v h) (by intro d hd; cases hd)))
def cl_20611 : CNF.NClause := [(69,true),(18,false),(2,true),(9,false),(27,true)]
theorem der_20611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20611 :=
  CNF.rup_sound cl_20611 [cl_20588,cl_20610] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20588 v h) (hints_cons _ _ _ (der_20610 v h) (by intro d hd; cases hd)))
def cl_20613 : CNF.NClause := [(65,true),(25,true),(3,true),(8,false),(18,true),(23,false)]
theorem der_20613 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20613 :=
  CNF.rup_sound cl_20613 [cl_234,cl_238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_234 v h) (hints_cons _ _ _ (inp_238 v h) (by intro d hd; cases hd)))
def cl_20617 : CNF.NClause := [(65,true),(25,false),(3,true),(8,false),(18,false),(23,false)]
theorem der_20617 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20617 :=
  CNF.rup_sound cl_20617 [cl_198,cl_15284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_198 v h) (hints_cons _ _ _ (der_15284 v h) (by intro d hd; cases hd)))
def cl_20625 : CNF.NClause := [(97,true),(37,true),(56,false),(52,true),(42,false),(32,false)]
theorem der_20625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20625 :=
  CNF.rup_sound cl_20625 [cl_2259,cl_18776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2259 v h) (hints_cons _ _ _ (der_18776 v h) (by intro d hd; cases hd)))
def cl_20638 : CNF.NClause := [(37,false),(78,false),(6,true),(66,false),(74,true),(91,false),(82,true)]
theorem der_20638 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20638 :=
  CNF.rup_sound cl_20638 [cl_4782,cl_4778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4782 v h) (hints_cons _ _ _ (inp_4778 v h) (by intro d hd; cases hd)))
def cl_20640 : CNF.NClause := [(71,true),(20,false),(1,false),(7,true),(19,true),(26,false)]
theorem der_20640 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20640 :=
  CNF.rup_sound cl_20640 [cl_20513,cl_591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20513 v h) (hints_cons _ _ _ (inp_591 v h) (by intro d hd; cases hd)))
def cl_20645 : CNF.NClause := [(94,true),(40,true),(50,true),(35,false),(56,false)]
theorem der_20645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20645 :=
  CNF.rup_sound cl_20645 [cl_19973,cl_18382,cl_2079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19973 v h) (hints_cons _ _ _ (der_18382 v h) (hints_cons _ _ _ (inp_2079 v h) (by intro d hd; cases hd))))
def cl_20647 : CNF.NClause := [(70,true),(20,false),(6,true),(3,false),(17,true),(28,true)]
theorem der_20647 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20647 :=
  CNF.rup_sound cl_20647 [cl_555,cl_559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_555 v h) (hints_cons _ _ _ (inp_559 v h) (by intro d hd; cases hd)))
def cl_20649 : CNF.NClause := [(68,true),(20,false),(4,false),(29,true),(8,false),(16,true)]
theorem der_20649 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20649 :=
  CNF.rup_sound cl_20649 [cl_20542,cl_429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20542 v h) (hints_cons _ _ _ (inp_429 v h) (by intro d hd; cases hd)))
def cl_20651 : CNF.NClause := [(75,true),(9,true),(3,false),(10,true),(16,true),(26,false)]
theorem der_20651 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20651 :=
  CNF.rup_sound cl_20651 [cl_17645,cl_863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17645 v h) (hints_cons _ _ _ (inp_863 v h) (by intro d hd; cases hd)))
def cl_20655 : CNF.NClause := [(78,true),(22,true),(6,true),(4,false),(15,false),(27,true)]
theorem der_20655 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20655 :=
  CNF.rup_sound cl_20655 [cl_1075,cl_1079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1075 v h) (hints_cons _ _ _ (inp_1079 v h) (by intro d hd; cases hd)))
def cl_20660 : CNF.NClause := [(78,true),(4,false),(6,true),(15,false),(27,true)]
theorem der_20660 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20660 :=
  CNF.rup_sound cl_20660 [cl_20432,cl_20655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20432 v h) (hints_cons _ _ _ (der_20655 v h) (by intro d hd; cases hd)))
def cl_20662 : CNF.NClause := [(96,true),(34,false),(56,false),(39,true),(49,false),(54,true)]
theorem der_20662 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20662 :=
  CNF.rup_sound cl_20662 [cl_2199,cl_15136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2199 v h) (hints_cons _ _ _ (der_15136 v h) (by intro d hd; cases hd)))
def cl_20663 : CNF.NClause := [(95,true),(38,true),(48,true),(43,false),(56,false),(53,true)]
theorem der_20663 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20663 :=
  CNF.rup_sound cl_20663 [cl_2139,cl_20321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2139 v h) (hints_cons _ _ _ (der_20321 v h) (by intro d hd; cases hd)))
def cl_20664 : CNF.NClause := [(93,true),(57,false),(56,false),(58,true),(59,true),(61,true)]
theorem der_20664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20664 :=
  CNF.rup_sound cl_20664 [cl_2029,cl_2045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2029 v h) (hints_cons _ _ _ (inp_2045 v h) (by intro d hd; cases hd)))
def cl_20665 : CNF.NClause := [(40,false),(82,true),(69,false),(9,true),(75,false),(81,false),(63,false)]
theorem der_20665 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20665 :=
  CNF.rup_sound cl_20665 [cl_5154,cl_5218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5154 v h) (hints_cons _ _ _ (inp_5218 v h) (by intro d hd; cases hd)))
def cl_20667 : CNF.NClause := [(71,true),(13,true),(7,true),(26,false),(19,true),(1,false)]
theorem der_20667 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20667 :=
  CNF.rup_sound cl_20667 [cl_607,cl_20640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_607 v h) (hints_cons _ _ _ (der_20640 v h) (by intro d hd; cases hd)))
def cl_20668 : CNF.NClause := [(71,true),(1,false),(7,true),(19,true),(26,false)]
theorem der_20668 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20668 :=
  CNF.rup_sound cl_20668 [cl_20513,cl_20667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20513 v h) (hints_cons _ _ _ (der_20667 v h) (by intro d hd; cases hd)))
def cl_20669 : CNF.NClause := [(97,true),(42,true),(37,true),(52,true),(32,false),(56,false)]
theorem der_20669 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20669 :=
  CNF.rup_sound cl_20669 [cl_2263,cl_2271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2263 v h) (hints_cons _ _ _ (inp_2271 v h) (by intro d hd; cases hd)))
def cl_20672 : CNF.NClause := [(67,true),(74,true),(29,true),(23,false),(19,true),(30,true),(21,true)]
theorem der_20672 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20672 :=
  CNF.rup_sound cl_20672 [cl_20550,cl_18789,cl_815,cl_18176,cl_20453,cl_375,cl_13757,cl_14447,cl_14436,cl_14455,cl_14445,cl_14454,cl_14432,cl_14428,cl_14449,cl_14446,cl_12133,cl_12093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20550 v h) (hints_cons _ _ _ (der_18789 v h) (hints_cons _ _ _ (inp_815 v h) (hints_cons _ _ _ (der_18176 v h) (hints_cons _ _ _ (der_20453 v h) (hints_cons _ _ _ (inp_375 v h) (hints_cons _ _ _ (inp_13757 v h) (hints_cons _ _ _ (inp_14447 v h) (hints_cons _ _ _ (inp_14436 v h) (hints_cons _ _ _ (inp_14455 v h) (hints_cons _ _ _ (inp_14445 v h) (hints_cons _ _ _ (inp_14454 v h) (hints_cons _ _ _ (inp_14432 v h) (hints_cons _ _ _ (inp_14428 v h) (hints_cons _ _ _ (inp_14449 v h) (hints_cons _ _ _ (inp_14446 v h) (hints_cons _ _ _ (inp_12133 v h) (hints_cons _ _ _ (inp_12093 v h) (by intro d hd; cases hd)))))))))))))))))))
def cl_20675 : CNF.NClause := [(24,false),(80,true),(7,true),(29,true),(15,false),(3,false)]
theorem der_20675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20675 :=
  CNF.rup_sound cl_20675 [cl_1187,cl_1191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1187 v h) (hints_cons _ _ _ (inp_1191 v h) (by intro d hd; cases hd)))
def cl_20676 : CNF.NClause := [(24,true),(80,true),(7,true),(29,true),(15,false),(3,false)]
theorem der_20676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20676 :=
  CNF.rup_sound cl_20676 [cl_1203,cl_1207] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1203 v h) (hints_cons _ _ _ (inp_1207 v h) (by intro d hd; cases hd)))
def cl_20677 : CNF.NClause := [(80,true),(3,false),(7,true),(29,true),(15,false)]
theorem der_20677 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20677 :=
  CNF.rup_sound cl_20677 [cl_20675,cl_20676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20675 v h) (hints_cons _ _ _ (der_20676 v h) (by intro d hd; cases hd)))
def cl_20678 : CNF.NClause := [(54,false),(83,false),(23,false),(74,true),(67,false),(81,false),(65,false)]
theorem der_20678 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20678 :=
  CNF.rup_sound cl_20678 [cl_6985,cl_6921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6985 v h) (hints_cons _ _ _ (inp_6921 v h) (by intro d hd; cases hd)))
def cl_20681 : CNF.NClause := [(95,true),(48,true),(43,false),(56,false),(38,true),(53,false)]
theorem der_20681 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20681 :=
  CNF.rup_sound cl_20681 [cl_2123,cl_2124] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2123 v h) (hints_cons _ _ _ (inp_2124 v h) (by intro d hd; cases hd)))
def cl_20687 : CNF.NClause := [(97,true),(52,true),(37,true),(56,false),(32,false)]
theorem der_20687 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20687 :=
  CNF.rup_sound cl_20687 [cl_20669,cl_20625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20669 v h) (hints_cons _ _ _ (der_20625 v h) (by intro d hd; cases hd)))
def cl_20692 : CNF.NClause := [(48,false),(70,true),(17,true),(64,false),(76,false),(77,false),(83,false)]
theorem der_20692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20692 :=
  CNF.rup_sound cl_20692 [cl_6150,cl_6214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6150 v h) (hints_cons _ _ _ (inp_6214 v h) (by intro d hd; cases hd)))
def cl_20698 : CNF.NClause := [(16,false),(29,true),(20,true),(8,false),(68,true),(12,false)]
theorem der_20698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20698 :=
  CNF.rup_sound cl_20698 [cl_433,cl_434] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_433 v h) (hints_cons _ _ _ (inp_434 v h) (by intro d hd; cases hd)))
def cl_20699 : CNF.NClause := [(29,true),(68,true),(12,false),(8,false),(20,true)]
theorem der_20699 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20699 :=
  CNF.rup_sound cl_20699 [cl_20542,cl_20698] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20542 v h) (hints_cons _ _ _ (der_20698 v h) (by intro d hd; cases hd)))
def cl_20702 : CNF.NClause := [(23,false),(29,false),(2,false),(19,true),(74,true),(6,true)]
theorem der_20702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20702 :=
  CNF.rup_sound cl_20702 [cl_20472,cl_779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20472 v h) (hints_cons _ _ _ (inp_779 v h) (by intro d hd; cases hd)))
def cl_20703 : CNF.NClause := [(23,true),(29,false),(6,true),(74,true),(19,true),(2,false)]
theorem der_20703 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20703 :=
  CNF.rup_sound cl_20703 [cl_799,cl_795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_799 v h) (hints_cons _ _ _ (inp_795 v h) (by intro d hd; cases hd)))
def cl_20704 : CNF.NClause := [(29,false),(2,false),(6,true),(19,true),(74,true)]
theorem der_20704 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20704 :=
  CNF.rup_sound cl_20704 [cl_20702,cl_20703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20702 v h) (hints_cons _ _ _ (der_20703 v h) (by intro d hd; cases hd)))
def cl_20710 : CNF.NClause := [(447,false),(9,true),(21,true),(88,true),(17,true),(463,true),(10,true)]
theorem der_20710 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20710 :=
  CNF.rup_sound cl_20710 [cl_14075,cl_14086,cl_14082,cl_14078,cl_9987,cl_17899,cl_14066] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14075 v h) (hints_cons _ _ _ (inp_14086 v h) (hints_cons _ _ _ (inp_14082 v h) (hints_cons _ _ _ (inp_14078 v h) (hints_cons _ _ _ (inp_9987 v h) (hints_cons _ _ _ (der_17899 v h) (hints_cons _ _ _ (inp_14066 v h) (by intro d hd; cases hd))))))))
def cl_20717 : CNF.NClause := [(66,true),(16,false),(1,false),(6,true),(11,false),(21,true)]
theorem der_20717 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20717 :=
  CNF.rup_sound cl_20717 [cl_275,cl_307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_275 v h) (hints_cons _ _ _ (inp_307 v h) (by intro d hd; cases hd)))
def cl_20721 : CNF.NClause := [(20,false),(70,true),(14,true),(3,false),(28,true),(6,true)]
theorem der_20721 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20721 :=
  CNF.rup_sound cl_20721 [cl_20647,cl_551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20647 v h) (hints_cons _ _ _ (inp_551 v h) (by intro d hd; cases hd)))
def cl_20727 : CNF.NClause := [(68,true),(12,false),(29,true),(20,true),(8,true),(16,false)]
theorem der_20727 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20727 :=
  CNF.rup_sound cl_20727 [cl_435,cl_436] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_435 v h) (hints_cons _ _ _ (inp_436 v h) (by intro d hd; cases hd)))
def cl_20731 : CNF.NClause := [(69,true),(27,false),(9,true),(11,false),(20,true),(2,false)]
theorem der_20731 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20731 :=
  CNF.rup_sound cl_20731 [cl_467,cl_475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_467 v h) (hints_cons _ _ _ (inp_475 v h) (by intro d hd; cases hd)))
def cl_20742 : CNF.NClause := [(24,false),(80,true),(7,false),(29,true),(3,false),(11,false)]
theorem der_20742 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20742 :=
  CNF.rup_sound cl_20742 [cl_1185,cl_1193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1185 v h) (hints_cons _ _ _ (inp_1193 v h) (by intro d hd; cases hd)))
def cl_20743 : CNF.NClause := [(24,true),(80,true),(29,true),(3,false),(11,false),(7,false)]
theorem der_20743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20743 :=
  CNF.rup_sound cl_20743 [cl_1209,cl_1201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1209 v h) (hints_cons _ _ _ (inp_1201 v h) (by intro d hd; cases hd)))
def cl_20744 : CNF.NClause := [(80,true),(11,false),(7,false),(29,true),(3,false)]
theorem der_20744 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20744 :=
  CNF.rup_sound cl_20744 [cl_20742,cl_20743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20742 v h) (hints_cons _ _ _ (der_20743 v h) (by intro d hd; cases hd)))
def cl_20745 : CNF.NClause := [(87,true),(4,false),(30,true),(2,false),(3,false),(1,false)]
theorem der_20745 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20745 :=
  CNF.rup_sound cl_20745 [cl_1634,cl_1633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1634 v h) (hints_cons _ _ _ (inp_1633 v h) (by intro d hd; cases hd)))
def cl_20747 : CNF.NClause := [(78,true),(4,false),(22,false),(6,true),(27,false),(15,false)]
theorem der_20747 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20747 :=
  CNF.rup_sound cl_20747 [cl_15079,cl_1031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15079 v h) (hints_cons _ _ _ (inp_1031 v h) (by intro d hd; cases hd)))
def cl_20748 : CNF.NClause := [(65,true),(25,false),(8,true),(3,false),(18,false),(23,true)]
theorem der_20748 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20748 :=
  CNF.rup_sound cl_20748 [cl_211,cl_215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_211 v h) (hints_cons _ _ _ (inp_215 v h) (by intro d hd; cases hd)))
def cl_20751 : CNF.NClause := [(18,false),(25,false),(8,true),(65,true),(3,false),(23,false)]
theorem der_20751 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20751 :=
  CNF.rup_sound cl_20751 [cl_199,cl_15284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_199 v h) (hints_cons _ _ _ (der_15284 v h) (by intro d hd; cases hd)))
def cl_20752 : CNF.NClause := [(18,true),(25,false),(8,true),(65,true),(3,false),(23,false)]
theorem der_20752 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20752 :=
  CNF.rup_sound cl_20752 [cl_207,cl_203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_207 v h) (hints_cons _ _ _ (inp_203 v h) (by intro d hd; cases hd)))
def cl_20753 : CNF.NClause := [(25,false),(65,true),(8,true),(23,false),(3,false)]
theorem der_20753 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20753 :=
  CNF.rup_sound cl_20753 [cl_20751,cl_20752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20751 v h) (hints_cons _ _ _ (der_20752 v h) (by intro d hd; cases hd)))
def cl_20754 : CNF.NClause := [(13,true),(65,true),(8,true),(25,true),(3,false),(23,false)]
theorem der_20754 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20754 :=
  CNF.rup_sound cl_20754 [cl_231,cl_239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_231 v h) (hints_cons _ _ _ (inp_239 v h) (by intro d hd; cases hd)))
def cl_20760 : CNF.NClause := [(26,true),(91,true),(0,false),(24,false),(6,true),(18,true)]
theorem der_20760 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20760 :=
  CNF.rup_sound cl_20760 [cl_1899,cl_1903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1899 v h) (hints_cons _ _ _ (inp_1903 v h) (by intro d hd; cases hd)))
def cl_20761 : CNF.NClause := [(26,false),(91,true),(24,false),(18,true),(6,true),(0,false)]
theorem der_20761 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20761 :=
  CNF.rup_sound cl_20761 [cl_1867,cl_1871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1867 v h) (hints_cons _ _ _ (inp_1871 v h) (by intro d hd; cases hd)))
def cl_20762 : CNF.NClause := [(91,true),(24,false),(0,false),(18,true),(6,true)]
theorem der_20762 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20762 :=
  CNF.rup_sound cl_20762 [cl_20760,cl_20761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20760 v h) (hints_cons _ _ _ (der_20761 v h) (by intro d hd; cases hd)))
def cl_20766 : CNF.NClause := [(64,true),(12,false),(2,false),(7,false),(25,true),(17,true)]
theorem der_20766 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20766 :=
  CNF.rup_sound cl_20766 [cl_169,cl_185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_169 v h) (hints_cons _ _ _ (inp_185 v h) (by intro d hd; cases hd)))
def cl_20769 : CNF.NClause := [(74,true),(6,true),(2,false),(10,true),(29,true),(23,false)]
theorem der_20769 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20769 :=
  CNF.rup_sound cl_20769 [cl_815,cl_20447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_815 v h) (hints_cons _ _ _ (der_20447 v h) (by intro d hd; cases hd)))
def cl_20782 : CNF.NClause := [(79,true),(14,false),(8,true),(2,false),(15,false),(21,true)]
theorem der_20782 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20782 :=
  CNF.rup_sound cl_20782 [cl_1107,cl_18940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1107 v h) (hints_cons _ _ _ (der_18940 v h) (by intro d hd; cases hd)))
def cl_20783 : CNF.NClause := [(78,true),(4,false),(6,true),(27,false),(15,false),(13,true)]
theorem der_20783 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20783 :=
  CNF.rup_sound cl_20783 [cl_1031,cl_1047] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1031 v h) (hints_cons _ _ _ (inp_1047 v h) (by intro d hd; cases hd)))
def cl_20785 : CNF.NClause := [(83,true),(4,false),(5,true),(11,false),(23,false),(17,true)]
theorem der_20785 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20785 :=
  CNF.rup_sound cl_20785 [cl_1355,cl_18764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1355 v h) (hints_cons _ _ _ (der_18764 v h) (by intro d hd; cases hd)))
def cl_20796 : CNF.NClause := [(74,true),(6,true),(2,false),(10,true),(23,false)]
theorem der_20796 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20796 :=
  CNF.rup_sound cl_20796 [cl_20769,cl_20446,cl_20704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20769 v h) (hints_cons _ _ _ (der_20446 v h) (hints_cons _ _ _ (der_20704 v h) (by intro d hd; cases hd))))
def cl_20797 : CNF.NClause := [(106,true),(40,true),(57,true),(41,true),(34,false),(47,false)]
theorem der_20797 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20797 :=
  CNF.rup_sound cl_20797 [cl_2855,cl_2871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2855 v h) (hints_cons _ _ _ (inp_2871 v h) (by intro d hd; cases hd)))
def cl_20799 : CNF.NClause := [(90,true),(28,false),(0,true),(11,false),(8,true),(19,true)]
theorem der_20799 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20799 :=
  CNF.rup_sound cl_20799 [cl_1820,cl_17883] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1820 v h) (hints_cons _ _ _ (der_17883 v h) (by intro d hd; cases hd)))
def cl_20801 : CNF.NClause := [(58,true),(120,true),(38,true),(47,false),(31,true),(54,false)]
theorem der_20801 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20801 :=
  CNF.rup_sound cl_20801 [cl_3748,cl_3752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3748 v h) (hints_cons _ _ _ (inp_3752 v h) (by intro d hd; cases hd)))
def cl_20803 : CNF.NClause := [(24,true),(91,false),(18,true),(26,true),(6,true),(0,true)]
theorem der_20803 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20803 :=
  CNF.rup_sound cl_20803 [cl_1916,cl_1920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1916 v h) (hints_cons _ _ _ (inp_1920 v h) (by intro d hd; cases hd)))
def cl_20805 : CNF.NClause := [(78,true),(4,false),(15,false),(6,true),(13,true)]
theorem der_20805 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20805 :=
  CNF.rup_sound cl_20805 [cl_20660,cl_20783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20660 v h) (hints_cons _ _ _ (der_20783 v h) (by intro d hd; cases hd)))
def cl_20807 : CNF.NClause := [(85,true),(19,true),(5,true),(3,false),(12,false),(21,true)]
theorem der_20807 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20807 :=
  CNF.rup_sound cl_20807 [cl_1499,cl_1531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1499 v h) (hints_cons _ _ _ (inp_1531 v h) (by intro d hd; cases hd)))
def cl_20809 : CNF.NClause := [(20,false),(15,false),(92,true),(5,true),(0,true)]
theorem der_20809 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20809 :=
  CNF.rup_sound cl_20809 [cl_18043,cl_15410,cl_1956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18043 v h) (hints_cons _ _ _ (der_15410 v h) (hints_cons _ _ _ (inp_1956 v h) (by intro d hd; cases hd))))
def cl_20810 : CNF.NClause := [(10,false),(15,false),(20,true),(0,true),(92,true),(5,true)]
theorem der_20810 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20810 :=
  CNF.rup_sound cl_20810 [cl_1940,cl_1972] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1940 v h) (hints_cons _ _ _ (inp_1972 v h) (by intro d hd; cases hd)))
def cl_20818 : CNF.NClause := [(15,false),(77,true),(18,true),(17,true),(16,false),(19,true)]
theorem der_20818 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20818 :=
  CNF.rup_sound cl_20818 [cl_1021,cl_989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1021 v h) (hints_cons _ _ _ (inp_989 v h) (by intro d hd; cases hd)))
def cl_20821 : CNF.NClause := [(7,true),(82,false),(6,true),(30,true),(9,true),(5,true)]
theorem der_20821 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20821 :=
  CNF.rup_sound cl_20821 [cl_1336,cl_1344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1336 v h) (hints_cons _ _ _ (inp_1344 v h) (by intro d hd; cases hd)))
def cl_20827 : CNF.NClause := [(4,true),(78,false),(15,true),(6,true),(13,true),(27,true)]
theorem der_20827 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20827 :=
  CNF.rup_sound cl_20827 [cl_1072,cl_1088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1072 v h) (hints_cons _ _ _ (inp_1088 v h) (by intro d hd; cases hd)))
def cl_20836 : CNF.NClause := [(23,true),(74,false),(6,true),(10,true),(19,true),(29,true)]
theorem der_20836 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20836 :=
  CNF.rup_sound cl_20836 [cl_831,cl_832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_831 v h) (hints_cons _ _ _ (inp_832 v h) (by intro d hd; cases hd)))
def cl_20843 : CNF.NClause := [(79,true),(8,false),(26,false),(21,false),(2,false),(15,true)]
theorem der_20843 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20843 :=
  CNF.rup_sound cl_20843 [cl_1097,cl_1101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1097 v h) (hints_cons _ _ _ (inp_1101 v h) (by intro d hd; cases hd)))
def cl_20844 : CNF.NClause := [(67,true),(21,false),(30,true),(20,false),(22,false),(23,false)]
theorem der_20844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20844 :=
  CNF.rup_sound cl_20844 [cl_353,cl_369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_353 v h) (hints_cons _ _ _ (inp_369 v h) (by intro d hd; cases hd)))
def cl_20851 : CNF.NClause := [(84,true),(13,true),(5,true),(24,true),(2,false),(16,false)]
theorem der_20851 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20851 :=
  CNF.rup_sound cl_20851 [cl_1463,cl_1431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1463 v h) (hints_cons _ _ _ (inp_1431 v h) (by intro d hd; cases hd)))
def cl_20852 : CNF.NClause := [(71,true),(7,false),(26,false),(13,true),(19,true),(20,false)]
theorem der_20852 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20852 :=
  CNF.rup_sound cl_20852 [cl_589,cl_590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_589 v h) (hints_cons _ _ _ (inp_590 v h) (by intro d hd; cases hd)))
def cl_20855 : CNF.NClause := [(734,true),(741,false),(717,true),(743,true),(721,true),(730,true),(718,true),(742,true),(723,true),(713,true),(726,true),(719,true),(731,true)]
theorem der_20855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20855 :=
  CNF.rup_sound cl_20855 [cl_11662,cl_11568,cl_11625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_11662 v h) (hints_cons _ _ _ (inp_11568 v h) (hints_cons _ _ _ (inp_11625 v h) (by intro d hd; cases hd))))
def cl_20861 : CNF.NClause := [(79,true),(15,false),(2,false),(8,false),(26,false),(21,false)]
theorem der_20861 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20861 :=
  CNF.rup_sound cl_20861 [cl_1093,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1093 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_20864 : CNF.NClause := [(67,true),(20,false),(30,true),(21,false),(23,false),(24,true)]
theorem der_20864 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20864 :=
  CNF.rup_sound cl_20864 [cl_20844,cl_373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20844 v h) (hints_cons _ _ _ (inp_373 v h) (by intro d hd; cases hd)))
def cl_20868 : CNF.NClause := [(1057,true),(1079,true),(1058,true),(1062,true),(1083,true),(1064,true),(1055,true),(1054,true),(1067,true),(1060,true),(1073,true),(1072,true),(1084,false)]
theorem der_20868 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20868 :=
  CNF.rup_sound cl_20868 [cl_13567,cl_13698,cl_13625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13567 v h) (hints_cons _ _ _ (inp_13698 v h) (hints_cons _ _ _ (inp_13625 v h) (by intro d hd; cases hd))))
def cl_20871 : CNF.NClause := [(1068,true),(1082,true),(1057,false),(1079,true),(1058,true),(1081,true),(1059,true),(1083,true),(1064,true),(1055,true),(1054,true),(1067,true),(1060,true),(1071,true),(1072,true)]
theorem der_20871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20871 :=
  CNF.rup_sound cl_20871 [cl_13693,cl_13601,cl_13646,cl_13729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13693 v h) (hints_cons _ _ _ (inp_13601 v h) (hints_cons _ _ _ (inp_13646 v h) (hints_cons _ _ _ (inp_13729 v h) (by intro d hd; cases hd)))))
def cl_20903 : CNF.NClause := [(291,false),(91,true),(24,true),(0,true),(5,true),(6,true),(18,true)]
theorem der_20903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20903 :=
  CNF.rup_sound cl_20903 [cl_13939,cl_13916,cl_13921,cl_13933,cl_13927,cl_9075,cl_1884,cl_13941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13939 v h) (hints_cons _ _ _ (inp_13916 v h) (hints_cons _ _ _ (inp_13921 v h) (hints_cons _ _ _ (inp_13933 v h) (hints_cons _ _ _ (inp_13927 v h) (hints_cons _ _ _ (inp_9075 v h) (hints_cons _ _ _ (inp_1884 v h) (hints_cons _ _ _ (inp_13941 v h) (by intro d hd; cases hd)))))))))
def cl_20940 : CNF.NClause := [(1080,false),(91,true),(24,true),(0,true),(30,true),(6,true),(18,true)]
theorem der_20940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20940 :=
  CNF.rup_sound cl_20940 [cl_14690,cl_14666,cl_14672,cl_14684,cl_14692,cl_13722,cl_1884,cl_14678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14690 v h) (hints_cons _ _ _ (inp_14666 v h) (hints_cons _ _ _ (inp_14672 v h) (hints_cons _ _ _ (inp_14684 v h) (hints_cons _ _ _ (inp_14692 v h) (hints_cons _ _ _ (inp_13722 v h) (hints_cons _ _ _ (inp_1884 v h) (hints_cons _ _ _ (inp_14678 v h) (by intro d hd; cases hd)))))))))
def cl_20943 : CNF.NClause := [(1080,true),(1063,true),(1077,true),(1065,true),(1078,true),(1074,true),(1073,true),(1081,true),(1059,true),(1058,true),(1064,true),(1055,true),(1067,true),(1060,true),(1084,false)]
theorem der_20943 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20943 :=
  CNF.rup_sound cl_20943 [cl_13606,cl_13676,cl_13668,cl_13636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13606 v h) (hints_cons _ _ _ (inp_13676 v h) (hints_cons _ _ _ (inp_13668 v h) (hints_cons _ _ _ (inp_13636 v h) (by intro d hd; cases hd)))))
def cl_20946 : CNF.NClause := [(684,false),(74,true),(701,true),(711,true),(10,true),(6,true),(18,true)]
theorem der_20946 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_20946 :=
  CNF.rup_sound cl_20946 [cl_14316,cl_14312,cl_14308,cl_11393,cl_20796,cl_14328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14316 v h) (hints_cons _ _ _ (inp_14312 v h) (hints_cons _ _ _ (inp_14308 v h) (hints_cons _ _ _ (inp_11393 v h) (hints_cons _ _ _ (der_20796 v h) (hints_cons _ _ _ (inp_14328 v h) (by intro d hd; cases hd)))))))
def cl_21014 : CNF.NClause := [(70,true),(14,false),(28,false),(20,true),(6,true),(17,false)]
theorem der_21014 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21014 :=
  CNF.rup_sound cl_21014 [cl_532,cl_531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_532 v h) (hints_cons _ _ _ (inp_531 v h) (by intro d hd; cases hd)))
def cl_21016 : CNF.NClause := [(80,true),(7,false),(29,true),(11,false),(15,false),(24,true)]
theorem der_21016 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21016 :=
  CNF.rup_sound cl_21016 [cl_1202,cl_20744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1202 v h) (hints_cons _ _ _ (der_20744 v h) (by intro d hd; cases hd)))
def cl_21028 : CNF.NClause := [(75,true),(26,false),(22,true),(9,false),(16,false),(10,true)]
theorem der_21028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21028 :=
  CNF.rup_sound cl_21028 [cl_854,cl_853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_854 v h) (hints_cons _ _ _ (inp_853 v h) (by intro d hd; cases hd)))
def cl_21041 : CNF.NClause := [(80,true),(7,false),(29,true),(11,false),(15,true),(24,true)]
theorem der_21041 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21041 :=
  CNF.rup_sound cl_21041 [cl_1210,cl_20744] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1210 v h) (hints_cons _ _ _ (der_20744 v h) (by intro d hd; cases hd)))
def cl_21080 : CNF.NClause := [(281,false),(74,true),(298,true),(308,true),(5,true),(10,true),(6,true)]
theorem der_21080 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21080 :=
  CNF.rup_sound cl_21080 [cl_13925,cl_13921,cl_13918,cl_8975,cl_20796,cl_13938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13925 v h) (hints_cons _ _ _ (inp_13921 v h) (hints_cons _ _ _ (inp_13918 v h) (hints_cons _ _ _ (inp_8975 v h) (hints_cons _ _ _ (der_20796 v h) (hints_cons _ _ _ (inp_13938 v h) (by intro d hd; cases hd)))))))
def cl_21091 : CNF.NClause := [(81,true),(23,false),(15,false),(28,false)]
theorem der_21091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21091 :=
  CNF.rup_sound cl_21091 [cl_15193,cl_15506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15193 v h) (hints_cons _ _ _ (der_15506 v h) (by intro d hd; cases hd)))
def cl_21093 : CNF.NClause := [(68,true),(8,false),(16,false),(4,true),(29,true),(20,true)]
theorem der_21093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21093 :=
  CNF.rup_sound cl_21093 [cl_438,cl_20699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_438 v h) (hints_cons _ _ _ (der_20699 v h) (by intro d hd; cases hd)))
def cl_21095 : CNF.NClause := [(72,true),(14,false),(11,false),(30,true),(10,true)]
theorem der_21095 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21095 :=
  CNF.rup_sound cl_21095 [cl_17632,cl_20298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17632 v h) (hints_cons _ _ _ (der_20298 v h) (by intro d hd; cases hd)))
def cl_21097 : CNF.NClause := [(91,true),(26,false),(0,true),(24,false),(18,true),(6,true)]
theorem der_21097 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21097 :=
  CNF.rup_sound cl_21097 [cl_1868,cl_1872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1868 v h) (hints_cons _ _ _ (inp_1872 v h) (by intro d hd; cases hd)))
def cl_21109 : CNF.NClause := [(83,true),(11,false),(26,false),(4,true),(23,true),(5,true)]
theorem der_21109 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21109 :=
  CNF.rup_sound cl_21109 [cl_1364,cl_1372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1364 v h) (hints_cons _ _ _ (inp_1372 v h) (by intro d hd; cases hd)))
def cl_21111 : CNF.NClause := [(88,true),(9,false),(13,true),(0,true),(21,false),(29,true)]
theorem der_21111 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21111 :=
  CNF.rup_sound cl_21111 [cl_1710,cl_1702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1710 v h) (hints_cons _ _ _ (inp_1702 v h) (by intro d hd; cases hd)))
def cl_21114 : CNF.NClause := [(76,true),(8,false),(27,true),(1,true),(10,true),(24,false)]
theorem der_21114 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21114 :=
  CNF.rup_sound cl_21114 [cl_942,cl_934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_942 v h) (hints_cons _ _ _ (inp_934 v h) (by intro d hd; cases hd)))
def cl_21158 : CNF.NClause := [(85,true),(3,false),(5,true),(27,true),(19,true),(21,false)]
theorem der_21158 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21158 :=
  CNF.rup_sound cl_21158 [cl_1515,cl_1519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1515 v h) (hints_cons _ _ _ (inp_1519 v h) (by intro d hd; cases hd)))
def cl_21164 : CNF.NClause := [(103,true),(42,false),(45,false),(41,true),(61,true),(44,true)]
theorem der_21164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21164 :=
  CNF.rup_sound cl_21164 [cl_20272,cl_2666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20272 v h) (hints_cons _ _ _ (inp_2666 v h) (by intro d hd; cases hd)))
def cl_21165 : CNF.NClause := [(100,true),(58,true),(42,false),(49,true),(33,false),(51,true)]
theorem der_21165 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21165 :=
  CNF.rup_sound cl_21165 [cl_2489,cl_18470] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2489 v h) (hints_cons _ _ _ (der_18470 v h) (by intro d hd; cases hd)))
def cl_21167 : CNF.NClause := [(111,true),(55,false),(42,false),(60,true),(34,false),(38,true)]
theorem der_21167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21167 :=
  CNF.rup_sound cl_21167 [cl_3171,cl_3179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3171 v h) (hints_cons _ _ _ (inp_3179 v h) (by intro d hd; cases hd)))
def cl_21168 : CNF.NClause := [(121,true),(50,true),(31,true),(53,true),(42,false),(39,false)]
theorem der_21168 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21168 :=
  CNF.rup_sound cl_21168 [cl_3802,cl_3834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3802 v h) (hints_cons _ _ _ (inp_3834 v h) (by intro d hd; cases hd)))
def cl_21169 : CNF.NClause := [(97,true),(56,true),(37,true),(42,false),(52,false),(47,false)]
theorem der_21169 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21169 :=
  CNF.rup_sound cl_21169 [cl_2276,cl_2275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2276 v h) (hints_cons _ _ _ (inp_2275 v h) (by intro d hd; cases hd)))
def cl_21175 : CNF.NClause := [(80,true),(11,false),(3,false),(7,true),(24,false),(29,true)]
theorem der_21175 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21175 :=
  CNF.rup_sound cl_21175 [cl_20677,cl_1195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20677 v h) (hints_cons _ _ _ (inp_1195 v h) (by intro d hd; cases hd)))
def cl_21176 : CNF.NClause := [(69,true),(11,false),(27,true),(18,true),(9,false),(20,true)]
theorem der_21176 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21176 :=
  CNF.rup_sound cl_21176 [cl_506,cl_505] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_506 v h) (hints_cons _ _ _ (inp_505 v h) (by intro d hd; cases hd)))
def cl_21190 : CNF.NClause := [(81,true),(23,false),(9,false),(1,true),(28,true),(15,false)]
theorem der_21190 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21190 :=
  CNF.rup_sound cl_21190 [cl_1250,cl_1254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1250 v h) (hints_cons _ _ _ (inp_1254 v h) (by intro d hd; cases hd)))
def cl_21205 : CNF.NClause := [(65,true),(3,false),(23,false),(18,true),(13,true),(25,false)]
theorem der_21205 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21205 :=
  CNF.rup_sound cl_21205 [cl_205,cl_20753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_205 v h) (hints_cons _ _ _ (der_20753 v h) (by intro d hd; cases hd)))
def cl_21207 : CNF.NClause := [(12,false),(64,true),(2,false),(22,true),(7,true),(25,false)]
theorem der_21207 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21207 :=
  CNF.rup_sound cl_21207 [cl_147,cl_155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_147 v h) (hints_cons _ _ _ (inp_155 v h) (by intro d hd; cases hd)))
def cl_21208 : CNF.NClause := [(12,true),(64,true),(22,true),(2,false),(25,false),(7,true)]
theorem der_21208 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21208 :=
  CNF.rup_sound cl_21208 [cl_151,cl_159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_151 v h) (hints_cons _ _ _ (inp_159 v h) (by intro d hd; cases hd)))
def cl_21209 : CNF.NClause := [(64,true),(2,false),(25,false),(22,true),(7,true)]
theorem der_21209 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21209 :=
  CNF.rup_sound cl_21209 [cl_21207,cl_21208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21207 v h) (hints_cons _ _ _ (der_21208 v h) (by intro d hd; cases hd)))
def cl_21218 : CNF.NClause := [(67,true),(22,true),(21,false),(30,true),(20,true),(24,false)]
theorem der_21218 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21218 :=
  CNF.rup_sound cl_21218 [cl_366,cl_358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_366 v h) (hints_cons _ _ _ (inp_358 v h) (by intro d hd; cases hd)))
def cl_21227 : CNF.NClause := [(63,true),(25,false),(4,true),(9,false),(24,false),(19,true)]
theorem der_21227 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21227 :=
  CNF.rup_sound cl_21227 [cl_74,cl_78] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_74 v h) (hints_cons _ _ _ (inp_78 v h) (by intro d hd; cases hd)))
def cl_21231 : CNF.NClause := [(8,true),(68,false),(16,true),(29,true),(20,true),(4,true)]
theorem der_21231 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21231 :=
  CNF.rup_sound cl_21231 [cl_444,cl_19920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_444 v h) (hints_cons _ _ _ (der_19920 v h) (by intro d hd; cases hd)))
def cl_21242 : CNF.NClause := [(67,true),(21,false),(24,false),(30,true),(22,false),(20,true)]
theorem der_21242 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21242 :=
  CNF.rup_sound cl_21242 [cl_354,cl_362] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_354 v h) (hints_cons _ _ _ (inp_362 v h) (by intro d hd; cases hd)))
def cl_21244 : CNF.NClause := [(67,true),(22,false),(21,true),(24,false),(30,true)]
theorem der_21244 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21244 :=
  CNF.rup_sound cl_21244 [cl_18176,cl_18057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18176 v h) (hints_cons _ _ _ (der_18057 v h) (by intro d hd; cases hd)))
def cl_21299 : CNF.NClause := [(708,true),(707,true),(703,true),(702,true),(701,true),(709,true),(686,true),(712,true),(683,true),(695,true),(711,true),(692,true),(700,false)]
theorem der_21299 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21299 :=
  CNF.rup_sound cl_21299 [cl_11374,cl_11318,cl_11384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_11374 v h) (hints_cons _ _ _ (inp_11318 v h) (hints_cons _ _ _ (inp_11384 v h) (by intro d hd; cases hd))))
def cl_21319 : CNF.NClause := [(17,true),(88,false),(13,true),(0,true),(29,true),(21,true)]
theorem der_21319 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21319 :=
  CNF.rup_sound cl_21319 [cl_1726,cl_19061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1726 v h) (hints_cons _ _ _ (der_19061 v h) (by intro d hd; cases hd)))
def cl_21327 : CNF.NClause := [(63,true),(25,false),(4,true),(19,true),(24,false)]
theorem der_21327 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21327 :=
  CNF.rup_sound cl_21327 [cl_21227,cl_18895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21227 v h) (hints_cons _ _ _ (der_18895 v h) (by intro d hd; cases hd)))
def cl_21342 : CNF.NClause := [(699,true),(707,false),(696,true),(690,true),(703,true),(682,true),(701,true),(709,true),(686,true),(683,true),(695,true),(711,true),(692,true)]
theorem der_21342 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21342 :=
  CNF.rup_sound cl_21342 [cl_11476,cl_11401,cl_11322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_11476 v h) (hints_cons _ _ _ (inp_11401 v h) (hints_cons _ _ _ (inp_11322 v h) (by intro d hd; cases hd))))
def cl_21447 : CNF.NClause := [(67,true),(24,false),(20,true),(30,true),(21,false)]
theorem der_21447 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21447 :=
  CNF.rup_sound cl_21447 [cl_21242,cl_21218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21242 v h) (hints_cons _ _ _ (der_21218 v h) (by intro d hd; cases hd)))
def cl_21452 : CNF.NClause := [(63,true),(25,true),(14,false),(4,true),(24,false),(19,true)]
theorem der_21452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21452 :=
  CNF.rup_sound cl_21452 [cl_106,cl_18133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_106 v h) (hints_cons _ _ _ (der_18133 v h) (by intro d hd; cases hd)))
def cl_21515 : CNF.NClause := [(84,true),(28,false),(16,false),(5,true),(13,true),(24,false)]
theorem der_21515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21515 :=
  CNF.rup_sound cl_21515 [cl_1416,cl_1415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1416 v h) (hints_cons _ _ _ (inp_1415 v h) (by intro d hd; cases hd)))
def cl_21516 : CNF.NClause := [(65,true),(25,false),(8,false),(3,false),(13,true),(18,true)]
theorem der_21516 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21516 :=
  CNF.rup_sound cl_21516 [cl_21205,cl_221] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21205 v h) (hints_cons _ _ _ (inp_221 v h) (by intro d hd; cases hd)))
def cl_21528 : CNF.NClause := [(79,true),(15,false),(8,false),(14,false),(26,true),(21,false)]
theorem der_21528 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21528 :=
  CNF.rup_sound cl_21528 [cl_1122,cl_1121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1122 v h) (hints_cons _ _ _ (inp_1121 v h) (by intro d hd; cases hd)))
def cl_21533 : CNF.NClause := [(81,true),(15,true),(1,true),(9,false),(28,false),(12,false)]
theorem der_21533 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21533 :=
  CNF.rup_sound cl_21533 [cl_1226,cl_1242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1226 v h) (hints_cons _ _ _ (inp_1242 v h) (by intro d hd; cases hd)))
def cl_21535 : CNF.NClause := [(79,true),(15,true),(21,false),(8,false),(14,false),(26,true)]
theorem der_21535 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21535 :=
  CNF.rup_sound cl_21535 [cl_1130,cl_1129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1130 v h) (hints_cons _ _ _ (inp_1129 v h) (by intro d hd; cases hd)))
def cl_21548 : CNF.NClause := [(49,false),(91,false),(65,false),(86,false),(18,true),(73,false)]
theorem der_21548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21548 :=
  CNF.rup_sound cl_21548 [cl_18714,cl_18700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18714 v h) (hints_cons _ _ _ (der_18700 v h) (by intro d hd; cases hd)))
def cl_21556 : CNF.NClause := [(81,true),(15,false),(9,false),(28,false),(12,false),(1,true)]
theorem der_21556 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21556 :=
  CNF.rup_sound cl_21556 [cl_21091,cl_1234] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21091 v h) (hints_cons _ _ _ (inp_1234 v h) (by intro d hd; cases hd)))
def cl_21562 : CNF.NClause := [(79,true),(26,true),(14,true),(8,false),(15,false),(21,false)]
theorem der_21562 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21562 :=
  CNF.rup_sound cl_21562 [cl_1125,cl_1126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1125 v h) (hints_cons _ _ _ (inp_1126 v h) (by intro d hd; cases hd)))
def cl_21566 : CNF.NClause := [(90,true),(28,false),(8,false),(0,true),(19,true),(22,false)]
theorem der_21566 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21566 :=
  CNF.rup_sound cl_21566 [cl_1802,cl_1806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1802 v h) (hints_cons _ _ _ (inp_1806 v h) (by intro d hd; cases hd)))
def cl_21576 : CNF.NClause := [(49,false),(91,false),(18,true),(86,true),(65,false),(73,false),(77,false)]
theorem der_21576 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21576 :=
  CNF.rup_sound cl_21576 [cl_6310,cl_6306] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6310 v h) (hints_cons _ _ _ (inp_6306 v h) (by intro d hd; cases hd)))
def cl_21592 : CNF.NClause := [(84,true),(28,true),(24,false),(5,true),(16,false),(13,true)]
theorem der_21592 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21592 :=
  CNF.rup_sound cl_21592 [cl_1448,cl_1447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1448 v h) (hints_cons _ _ _ (inp_1447 v h) (by intro d hd; cases hd)))
def cl_21597 : CNF.NClause := [(81,true),(9,false),(15,false),(28,true),(12,false),(1,true)]
theorem der_21597 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21597 :=
  CNF.rup_sound cl_21597 [cl_21190,cl_20478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21190 v h) (hints_cons _ _ _ (der_20478 v h) (by intro d hd; cases hd)))
def cl_21599 : CNF.NClause := [(64,true),(25,true),(22,false),(12,false),(7,false),(17,false)]
theorem der_21599 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21599 :=
  CNF.rup_sound cl_21599 [cl_161,cl_162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_161 v h) (hints_cons _ _ _ (inp_162 v h) (by intro d hd; cases hd)))
def cl_21609 : CNF.NClause := [(63,true),(14,false),(24,false),(19,true),(4,true)]
theorem der_21609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21609 :=
  CNF.rup_sound cl_21609 [cl_21327,cl_21452] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21327 v h) (hints_cons _ _ _ (der_21452 v h) (by intro d hd; cases hd)))
def cl_21617 : CNF.NClause := [(83,true),(11,false),(17,true),(26,false),(5,true),(4,true)]
theorem der_21617 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21617 :=
  CNF.rup_sound cl_21617 [cl_21109,cl_1356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21109 v h) (hints_cons _ _ _ (inp_1356 v h) (by intro d hd; cases hd)))
def cl_21619 : CNF.NClause := [(64,true),(25,false),(17,true),(7,false),(12,false),(22,false)]
theorem der_21619 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21619 :=
  CNF.rup_sound cl_21619 [cl_137,cl_138] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_137 v h) (hints_cons _ _ _ (inp_138 v h) (by intro d hd; cases hd)))
def cl_21625 : CNF.NClause := [(25,true),(65,true),(8,false),(18,true),(13,true),(3,false)]
theorem der_21625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21625 :=
  CNF.rup_sound cl_21625 [cl_237,cl_253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_237 v h) (hints_cons _ _ _ (inp_253 v h) (by intro d hd; cases hd)))
def cl_21626 : CNF.NClause := [(65,true),(8,false),(18,true),(3,false),(13,true)]
theorem der_21626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21626 :=
  CNF.rup_sound cl_21626 [cl_21516,cl_21625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21516 v h) (hints_cons _ _ _ (der_21625 v h) (by intro d hd; cases hd)))
def cl_21629 : CNF.NClause := [(81,true),(9,false),(1,true),(15,true),(28,true),(12,false)]
theorem der_21629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21629 :=
  CNF.rup_sound cl_21629 [cl_1258,cl_1274] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1258 v h) (hints_cons _ _ _ (inp_1274 v h) (by intro d hd; cases hd)))
def cl_21661 : CNF.NClause := [(708,true),(693,true),(710,true),(698,true),(702,true),(701,true),(709,true),(686,true),(712,true),(683,true),(695,true),(711,true),(692,true),(688,true),(700,false)]
theorem der_21661 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21661 :=
  CNF.rup_sound cl_21661 [cl_11321,cl_21299,cl_11341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_11321 v h) (hints_cons _ _ _ (der_21299 v h) (hints_cons _ _ _ (inp_11341 v h) (by intro d hd; cases hd))))
def cl_21705 : CNF.NClause := [(62,true),(28,false),(30,true),(26,false),(27,true),(29,true)]
theorem der_21705 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21705 :=
  CNF.rup_sound cl_21705 [cl_53,cl_54] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_53 v h) (hints_cons _ _ _ (inp_54 v h) (by intro d hd; cases hd)))
def cl_21708 : CNF.NClause := [(81,true),(28,false),(9,false),(15,false),(12,true),(1,true)]
theorem der_21708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21708 :=
  CNF.rup_sound cl_21708 [cl_21091,cl_1238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21091 v h) (hints_cons _ _ _ (inp_1238 v h) (by intro d hd; cases hd)))
def cl_21711 : CNF.NClause := [(25,true),(64,true),(17,false),(7,false),(12,true),(22,false)]
theorem der_21711 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21711 :=
  CNF.rup_sound cl_21711 [cl_165,cl_166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_165 v h) (hints_cons _ _ _ (inp_166 v h) (by intro d hd; cases hd)))
def cl_21751 : CNF.NClause := [(64,true),(25,false),(17,true),(22,false),(12,true),(7,false)]
theorem der_21751 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21751 :=
  CNF.rup_sound cl_21751 [cl_141,cl_142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_141 v h) (hints_cons _ _ _ (inp_142 v h) (by intro d hd; cases hd)))
def cl_21763 : CNF.NClause := [(81,true),(9,false),(12,true),(1,true),(15,true),(28,false)]
theorem der_21763 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21763 :=
  CNF.rup_sound cl_21763 [cl_1230,cl_1246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1230 v h) (hints_cons _ _ _ (inp_1246 v h) (by intro d hd; cases hd)))
def cl_21767 : CNF.NClause := [(62,true),(28,false),(25,false),(27,true),(30,true),(29,true)]
theorem der_21767 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21767 :=
  CNF.rup_sound cl_21767 [cl_21705,cl_17658] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21705 v h) (hints_cons _ _ _ (der_17658 v h) (by intro d hd; cases hd)))
def cl_21780 : CNF.NClause := [(84,true),(28,false),(24,false),(5,true),(13,true)]
theorem der_21780 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21780 :=
  CNF.rup_sound cl_21780 [cl_21515,cl_18782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21515 v h) (hints_cons _ _ _ (der_18782 v h) (by intro d hd; cases hd)))
def cl_21786 : CNF.NClause := [(64,true),(12,false),(22,true),(7,false),(25,false),(17,false)]
theorem der_21786 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21786 :=
  CNF.rup_sound cl_21786 [cl_145,cl_146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_145 v h) (hints_cons _ _ _ (inp_146 v h) (by intro d hd; cases hd)))
def cl_21796 : CNF.NClause := [(83,true),(26,false),(17,false),(5,true),(4,true)]
theorem der_21796 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21796 :=
  CNF.rup_sound cl_21796 [cl_15548,cl_21109,cl_1368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15548 v h) (hints_cons _ _ _ (der_21109 v h) (hints_cons _ _ _ (inp_1368 v h) (by intro d hd; cases hd))))
def cl_21807 : CNF.NClause := [(64,true),(12,true),(7,false),(25,false),(17,false),(22,true)]
theorem der_21807 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21807 :=
  CNF.rup_sound cl_21807 [cl_150,cl_149] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_150 v h) (hints_cons _ _ _ (inp_149 v h) (by intro d hd; cases hd)))
def cl_21818 : CNF.NClause := [(66,true),(16,true),(1,true),(21,false),(6,true),(25,false)]
theorem der_21818 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21818 :=
  CNF.rup_sound cl_21818 [cl_268,cl_272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_268 v h) (hints_cons _ _ _ (inp_272 v h) (by intro d hd; cases hd)))
def cl_21827 : CNF.NClause := [(83,true),(23,false),(17,true),(5,true),(26,false),(4,true)]
theorem der_21827 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21827 :=
  CNF.rup_sound cl_21827 [cl_1360,cl_1356] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1360 v h) (hints_cons _ _ _ (inp_1356 v h) (by intro d hd; cases hd)))
def cl_21829 : CNF.NClause := [(64,true),(12,false),(25,false),(22,true),(17,true),(7,false)]
theorem der_21829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21829 :=
  CNF.rup_sound cl_21829 [cl_153,cl_154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_153 v h) (hints_cons _ _ _ (inp_154 v h) (by intro d hd; cases hd)))
def cl_21842 : CNF.NClause := [(30,false),(9,false),(82,true)]
theorem der_21842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21842 :=
  CNF.rup_sound cl_21842 [cl_15559,cl_15598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15559 v h) (hints_cons _ _ _ (der_15598 v h) (by intro d hd; cases hd)))
def cl_21843 : CNF.NClause := [(6,false),(8,false),(82,true)]
theorem der_21843 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21843 :=
  CNF.rup_sound cl_21843 [cl_17607,cl_15595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17607 v h) (hints_cons _ _ _ (der_15595 v h) (by intro d hd; cases hd)))
def cl_21844 : CNF.NClause := [(61,false),(118,true),(31,false)]
theorem der_21844 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21844 :=
  CNF.rup_sound cl_21844 [cl_15150,cl_15466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15150 v h) (hints_cons _ _ _ (der_15466 v h) (by intro d hd; cases hd)))
def cl_21845 : CNF.NClause := [(87,true),(30,false),(0,false)]
theorem der_21845 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21845 :=
  CNF.rup_sound cl_21845 [cl_15149,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15149 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_21846 : CNF.NClause := [(81,true),(1,false),(9,true),(12,false)]
theorem der_21846 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21846 :=
  CNF.rup_sound cl_21846 [cl_19126,cl_17623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19126 v h) (hints_cons _ _ _ (der_17623 v h) (by intro d hd; cases hd)))
def cl_21847 : CNF.NClause := [(70,true),(14,false),(6,false),(3,true)]
theorem der_21847 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21847 :=
  CNF.rup_sound cl_21847 [cl_19573,cl_18578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19573 v h) (hints_cons _ _ _ (der_18578 v h) (by intro d hd; cases hd)))
def cl_21848 : CNF.NClause := [(6,false),(74,true),(10,true),(2,false)]
theorem der_21848 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21848 :=
  CNF.rup_sound cl_21848 [cl_18474,cl_19906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18474 v h) (hints_cons _ _ _ (der_19906 v h) (by intro d hd; cases hd)))
def cl_21849 : CNF.NClause := [(63,true),(9,true),(25,false),(14,false)]
theorem der_21849 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21849 :=
  CNF.rup_sound cl_21849 [cl_18134,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18134 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_21850 : CNF.NClause := [(86,true),(1,false),(5,true),(22,false)]
theorem der_21850 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21850 :=
  CNF.rup_sound cl_21850 [cl_18514,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18514 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_21851 : CNF.NClause := [(90,true),(22,false),(8,false),(28,true)]
theorem der_21851 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21851 :=
  CNF.rup_sound cl_21851 [cl_20444,cl_20427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20444 v h) (hints_cons _ _ _ (der_20427 v h) (by intro d hd; cases hd)))
def cl_21852 : CNF.NClause := [(87,true),(30,false),(0,false),(2,true)]
theorem der_21852 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21852 :=
  CNF.rup_sound cl_21852 [cl_14883,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14883 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_21853 : CNF.NClause := [(87,true),(3,true),(2,false),(1,false)]
theorem der_21853 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21853 :=
  CNF.rup_sound cl_21853 [cl_18089,cl_15450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18089 v h) (hints_cons _ _ _ (der_15450 v h) (by intro d hd; cases hd)))
def cl_21854 : CNF.NClause := [(91,true),(24,false),(18,false),(26,false)]
theorem der_21854 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21854 :=
  CNF.rup_sound cl_21854 [cl_15077,cl_15482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15077 v h) (hints_cons _ _ _ (der_15482 v h) (by intro d hd; cases hd)))
def cl_21855 : CNF.NClause := [(64,true),(25,false),(17,false),(22,false)]
theorem der_21855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21855 :=
  CNF.rup_sound cl_21855 [cl_15175,cl_15494] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15175 v h) (hints_cons _ _ _ (der_15494 v h) (by intro d hd; cases hd)))
def cl_21856 : CNF.NClause := [(19,false),(74,true),(29,false),(10,true)]
theorem der_21856 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21856 :=
  CNF.rup_sound cl_21856 [cl_20446,cl_19906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20446 v h) (hints_cons _ _ _ (der_19906 v h) (by intro d hd; cases hd)))
def cl_21857 : CNF.NClause := [(90,true),(28,false),(19,false),(22,false)]
theorem der_21857 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21857 :=
  CNF.rup_sound cl_21857 [cl_15403,cl_15288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15403 v h) (hints_cons _ _ _ (der_15288 v h) (by intro d hd; cases hd)))
def cl_21858 : CNF.NClause := [(9,false),(6,false),(82,true),(8,true)]
theorem der_21858 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21858 :=
  CNF.rup_sound cl_21858 [cl_17610,cl_21842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17610 v h) (hints_cons _ _ _ (der_21842 v h) (by intro d hd; cases hd)))
def cl_21859 : CNF.NClause := [(78,true),(15,false),(22,false),(27,true)]
theorem der_21859 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21859 :=
  CNF.rup_sound cl_21859 [cl_20432,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20432 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_21860 : CNF.NClause := [(68,true),(16,false),(20,false),(29,false)]
theorem der_21860 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21860 :=
  CNF.rup_sound cl_21860 [cl_15516,cl_15191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15516 v h) (hints_cons _ _ _ (der_15191 v h) (by intro d hd; cases hd)))
def cl_21861 : CNF.NClause := [(23,false),(74,true),(2,false),(10,true)]
theorem der_21861 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21861 :=
  CNF.rup_sound cl_21861 [cl_20796,cl_21848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20796 v h) (hints_cons _ _ _ (der_21848 v h) (by intro d hd; cases hd)))
def cl_21862 : CNF.NClause := [(118,true),(31,false),(34,true),(32,false)]
theorem der_21862 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21862 :=
  CNF.rup_sound cl_21862 [cl_20255,cl_21844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20255 v h) (hints_cons _ _ _ (der_21844 v h) (by intro d hd; cases hd)))
def cl_21863 : CNF.NClause := [(118,true),(31,false),(34,true),(35,false)]
theorem der_21863 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21863 :=
  CNF.rup_sound cl_21863 [cl_19999,cl_21844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19999 v h) (hints_cons _ _ _ (der_21844 v h) (by intro d hd; cases hd)))
def cl_21864 : CNF.NClause := [(6,false),(74,true),(23,false),(10,true)]
theorem der_21864 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21864 :=
  CNF.rup_sound cl_21864 [cl_18789,cl_19906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18789 v h) (hints_cons _ _ _ (der_19906 v h) (by intro d hd; cases hd)))
def cl_21865 : CNF.NClause := [(63,true),(25,false),(4,false),(9,true)]
theorem der_21865 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21865 :=
  CNF.rup_sound cl_21865 [cl_18732,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18732 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_21866 : CNF.NClause := [(63,true),(9,true),(24,false),(25,false)]
theorem der_21866 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21866 :=
  CNF.rup_sound cl_21866 [cl_18895,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18895 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_21867 : CNF.NClause := [(91,true),(24,false),(18,false),(6,false)]
theorem der_21867 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21867 :=
  CNF.rup_sound cl_21867 [cl_19915,cl_21854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19915 v h) (hints_cons _ _ _ (der_21854 v h) (by intro d hd; cases hd)))
def cl_21868 : CNF.NClause := [(91,true),(18,false),(12,false),(6,false)]
theorem der_21868 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21868 :=
  CNF.rup_sound cl_21868 [cl_20493,cl_19858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20493 v h) (hints_cons _ _ _ (der_19858 v h) (by intro d hd; cases hd)))
def cl_21869 : CNF.NClause := [(91,true),(12,false),(18,false),(26,false)]
theorem der_21869 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21869 :=
  CNF.rup_sound cl_21869 [cl_20510,cl_21868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20510 v h) (hints_cons _ _ _ (der_21868 v h) (by intro d hd; cases hd)))
def cl_21870 : CNF.NClause := [(81,true),(23,false),(9,true),(12,false)]
theorem der_21870 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21870 :=
  CNF.rup_sound cl_21870 [cl_19867,cl_17623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19867 v h) (hints_cons _ _ _ (der_17623 v h) (by intro d hd; cases hd)))
def cl_21871 : CNF.NClause := [(63,true),(14,false),(24,false),(9,true)]
theorem der_21871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21871 :=
  CNF.rup_sound cl_21871 [cl_20246,cl_18133] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20246 v h) (hints_cons _ _ _ (der_18133 v h) (by intro d hd; cases hd)))
def cl_21872 : CNF.NClause := [(63,true),(14,false),(4,false),(9,true)]
theorem der_21872 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21872 :=
  CNF.rup_sound cl_21872 [cl_20386,cl_18555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20386 v h) (hints_cons _ _ _ (der_18555 v h) (by intro d hd; cases hd)))
def cl_21873 : CNF.NClause := [(87,true),(0,false),(4,false),(3,true)]
theorem der_21873 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21873 :=
  CNF.rup_sound cl_21873 [cl_19557,cl_21845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19557 v h) (hints_cons _ _ _ (der_21845 v h) (by intro d hd; cases hd)))
def cl_21874 : CNF.NClause := [(91,true),(6,false),(0,false),(26,true)]
theorem der_21874 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21874 :=
  CNF.rup_sound cl_21874 [cl_20109,cl_19858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20109 v h) (hints_cons _ _ _ (der_19858 v h) (by intro d hd; cases hd)))
def cl_21875 : CNF.NClause := [(64,true),(7,true),(25,false),(22,false)]
theorem der_21875 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21875 :=
  CNF.rup_sound cl_21875 [cl_19779,cl_21855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19779 v h) (hints_cons _ _ _ (der_21855 v h) (by intro d hd; cases hd)))
def cl_21876 : CNF.NClause := [(239,false),(86,true),(3,true),(5,true)]
theorem der_21876 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21876 :=
  CNF.rup_sound cl_21876 [cl_19069,cl_13877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19069 v h) (hints_cons _ _ _ (inp_13877 v h) (by intro d hd; cases hd)))
def cl_21877 : CNF.NClause := [(6,false),(74,true),(29,false),(10,true)]
theorem der_21877 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21877 :=
  CNF.rup_sound cl_21877 [cl_20466,cl_21856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20466 v h) (hints_cons _ _ _ (der_21856 v h) (by intro d hd; cases hd)))
def cl_21878 : CNF.NClause := [(17,false),(6,false),(70,true),(3,true)]
theorem der_21878 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21878 :=
  CNF.rup_sound cl_21878 [cl_19667,cl_18578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19667 v h) (hints_cons _ _ _ (der_18578 v h) (by intro d hd; cases hd)))
def cl_21879 : CNF.NClause := [(64,true),(17,false),(22,false),(7,true)]
theorem der_21879 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21879 :=
  CNF.rup_sound cl_21879 [cl_19709,cl_21855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19709 v h) (hints_cons _ _ _ (der_21855 v h) (by intro d hd; cases hd)))
def cl_21882 : CNF.NClause := [(87,true),(4,false),(2,false),(3,true)]
theorem der_21882 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21882 :=
  CNF.rup_sound cl_21882 [cl_19531,cl_15450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19531 v h) (hints_cons _ _ _ (der_15450 v h) (by intro d hd; cases hd)))
def cl_21884 : CNF.NClause := [(81,true),(28,false),(1,true),(15,true),(12,false)]
theorem der_21884 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21884 :=
  CNF.rup_sound cl_21884 [cl_21533,cl_17623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21533 v h) (hints_cons _ _ _ (der_17623 v h) (by intro d hd; cases hd)))
def cl_21885 : CNF.NClause := [(81,true),(28,false),(1,true),(15,true),(9,false)]
theorem der_21885 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21885 :=
  CNF.rup_sound cl_21885 [cl_21763,cl_21884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21763 v h) (hints_cons _ _ _ (der_21884 v h) (by intro d hd; cases hd)))
def cl_21886 : CNF.NClause := [(81,true),(28,false),(9,true),(12,false),(15,false)]
theorem der_21886 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21886 :=
  CNF.rup_sound cl_21886 [cl_17618,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17618 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_21887 : CNF.NClause := [(81,true),(15,false),(1,true),(23,false),(9,false)]
theorem der_21887 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21887 :=
  CNF.rup_sound cl_21887 [cl_21190,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21190 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_21888 : CNF.NClause := [(81,true),(1,true),(15,false),(12,false),(9,true)]
theorem der_21888 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21888 :=
  CNF.rup_sound cl_21888 [cl_19129,cl_21886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19129 v h) (hints_cons _ _ _ (der_21886 v h) (by intro d hd; cases hd)))
def cl_21889 : CNF.NClause := [(81,true),(12,false),(1,true),(15,true),(9,false)]
theorem der_21889 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21889 :=
  CNF.rup_sound cl_21889 [cl_21629,cl_21884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21629 v h) (hints_cons _ _ _ (der_21884 v h) (by intro d hd; cases hd)))
def cl_21890 : CNF.NClause := [(87,true),(1,false),(4,false),(3,true),(30,true)]
theorem der_21890 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21890 :=
  CNF.rup_sound cl_21890 [cl_18560,cl_21882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18560 v h) (hints_cons _ _ _ (der_21882 v h) (by intro d hd; cases hd)))
def cl_21891 : CNF.NClause := [(87,true),(30,false),(2,true),(0,true),(1,false)]
theorem der_21891 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21891 :=
  CNF.rup_sound cl_21891 [cl_14978,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14978 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_21892 : CNF.NClause := [(90,true),(28,true),(19,true),(11,false),(8,false)]
theorem der_21892 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21892 :=
  CNF.rup_sound cl_21892 [cl_20485,cl_20427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20485 v h) (hints_cons _ _ _ (der_20427 v h) (by intro d hd; cases hd)))
def cl_21893 : CNF.NClause := [(64,true),(22,false),(17,true),(25,false),(7,true)]
theorem der_21893 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21893 :=
  CNF.rup_sound cl_21893 [cl_19778,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19778 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_21894 : CNF.NClause := [(64,true),(25,true),(7,true),(22,false),(17,false)]
theorem der_21894 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21894 :=
  CNF.rup_sound cl_21894 [cl_19708,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19708 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_21895 : CNF.NClause := [(71,true),(13,false),(7,true),(1,false),(19,true)]
theorem der_21895 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21895 :=
  CNF.rup_sound cl_21895 [cl_18053,cl_20668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18053 v h) (hints_cons _ _ _ (der_20668 v h) (by intro d hd; cases hd)))
def cl_21896 : CNF.NClause := [(66,true),(6,false),(16,true),(1,false),(21,true)]
theorem der_21896 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21896 :=
  CNF.rup_sound cl_21896 [cl_19620,cl_18766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19620 v h) (hints_cons _ _ _ (der_18766 v h) (by intro d hd; cases hd)))
def cl_21897 : CNF.NClause := [(4,false),(83,true),(5,true),(26,true),(17,false)]
theorem der_21897 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21897 :=
  CNF.rup_sound cl_21897 [cl_19506,cl_17999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19506 v h) (hints_cons _ _ _ (der_17999 v h) (by intro d hd; cases hd)))
def cl_21898 : CNF.NClause := [(83,true),(26,true),(5,true),(4,false),(11,false)]
theorem der_21898 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21898 :=
  CNF.rup_sound cl_21898 [cl_18613,cl_17999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18613 v h) (hints_cons _ _ _ (der_17999 v h) (by intro d hd; cases hd)))
def cl_21899 : CNF.NClause := [(87,true),(30,false),(0,true),(2,true),(4,false)]
theorem der_21899 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21899 :=
  CNF.rup_sound cl_21899 [cl_14848,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14848 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_21901 : CNF.NClause := [(63,true),(14,false),(9,true),(4,false),(19,false)]
theorem der_21901 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21901 :=
  CNF.rup_sound cl_21901 [cl_19622,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19622 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_21902 : CNF.NClause := [(63,true),(4,false),(9,true),(24,false),(19,true)]
theorem der_21902 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21902 :=
  CNF.rup_sound cl_21902 [cl_17844,cl_18555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17844 v h) (hints_cons _ _ _ (der_18555 v h) (by intro d hd; cases hd)))
def cl_21903 : CNF.NClause := [(13,false),(0,false),(9,true),(88,true),(21,true)]
theorem der_21903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21903 :=
  CNF.rup_sound cl_21903 [cl_17899,cl_18164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17899 v h) (hints_cons _ _ _ (der_18164 v h) (by intro d hd; cases hd)))
def cl_21904 : CNF.NClause := [(16,true),(68,true),(8,true),(12,false),(20,false)]
theorem der_21904 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21904 :=
  CNF.rup_sound cl_21904 [cl_17791,cl_17664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17791 v h) (hints_cons _ _ _ (der_17664 v h) (by intro d hd; cases hd)))
def cl_21905 : CNF.NClause := [(90,true),(22,false),(19,false),(11,false),(8,true)]
theorem der_21905 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21905 :=
  CNF.rup_sound cl_21905 [cl_20239,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20239 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_21906 : CNF.NClause := [(25,false),(18,false),(8,true),(3,false),(65,true)]
theorem der_21906 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21906 :=
  CNF.rup_sound cl_21906 [cl_20748,cl_20753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20748 v h) (hints_cons _ _ _ (der_20753 v h) (by intro d hd; cases hd)))
def cl_21907 : CNF.NClause := [(65,true),(23,false),(8,true),(13,true),(3,false)]
theorem der_21907 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21907 :=
  CNF.rup_sound cl_21907 [cl_20754,cl_20753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20754 v h) (hints_cons _ _ _ (der_20753 v h) (by intro d hd; cases hd)))
def cl_21908 : CNF.NClause := [(16,false),(68,true),(29,true),(20,true),(12,false)]
theorem der_21908 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21908 :=
  CNF.rup_sound cl_21908 [cl_20727,cl_20699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20727 v h) (hints_cons _ _ _ (der_20699 v h) (by intro d hd; cases hd)))
def cl_21909 : CNF.NClause := [(90,true),(11,false),(22,false),(28,false),(8,true)]
theorem der_21909 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21909 :=
  CNF.rup_sound cl_21909 [cl_17883,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17883 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_21910 : CNF.NClause := [(90,true),(11,false),(28,true),(19,true),(22,false)]
theorem der_21910 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21910 :=
  CNF.rup_sound cl_21910 [cl_19076,cl_20427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19076 v h) (hints_cons _ _ _ (der_20427 v h) (by intro d hd; cases hd)))
def cl_21911 : CNF.NClause := [(84,true),(28,false),(13,false),(5,true),(24,false)]
theorem der_21911 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21911 :=
  CNF.rup_sound cl_21911 [cl_17894,cl_15185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17894 v h) (hints_cons _ _ _ (der_15185 v h) (by intro d hd; cases hd)))
def cl_21912 : CNF.NClause := [(10,false),(15,false),(0,true),(92,true),(5,true)]
theorem der_21912 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21912 :=
  CNF.rup_sound cl_21912 [cl_20810,cl_20809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20810 v h) (hints_cons _ _ _ (der_20809 v h) (by intro d hd; cases hd)))
def cl_21913 : CNF.NClause := [(84,true),(13,false),(5,true),(28,false),(16,false)]
theorem der_21913 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21913 :=
  CNF.rup_sound cl_21913 [cl_17638,cl_15185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17638 v h) (hints_cons _ _ _ (der_15185 v h) (by intro d hd; cases hd)))
def cl_21914 : CNF.NClause := [(86,true),(14,false),(22,false),(1,true),(5,true)]
theorem der_21914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21914 :=
  CNF.rup_sound cl_21914 [cl_17775,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17775 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_21916 : CNF.NClause := [(54,false),(89,true),(23,true),(67,false),(74,false)]
theorem der_21916 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21916 :=
  CNF.rup_sound cl_21916 [cl_20100,cl_20097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20100 v h) (hints_cons _ _ _ (der_20097 v h) (by intro d hd; cases hd)))
def cl_21917 : CNF.NClause := [(87,true),(0,false),(2,false),(3,true),(30,true)]
theorem der_21917 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21917 :=
  CNF.rup_sound cl_21917 [cl_19537,cl_21882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19537 v h) (hints_cons _ _ _ (der_21882 v h) (by intro d hd; cases hd)))
def cl_21918 : CNF.NClause := [(92,true),(0,false),(5,true),(25,false),(10,true)]
theorem der_21918 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21918 :=
  CNF.rup_sound cl_21918 [cl_18303,cl_18055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18303 v h) (hints_cons _ _ _ (der_18055 v h) (by intro d hd; cases hd)))
def cl_21919 : CNF.NClause := [(42,false),(72,true),(66,false),(90,false),(11,true)]
theorem der_21919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21919 :=
  CNF.rup_sound cl_21919 [cl_19493,cl_19489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19493 v h) (hints_cons _ _ _ (der_19489 v h) (by intro d hd; cases hd)))
def cl_21920 : CNF.NClause := [(59,false),(28,true),(70,false),(84,false),(90,false)]
theorem der_21920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21920 :=
  CNF.rup_sound cl_21920 [cl_20284,cl_19328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20284 v h) (hints_cons _ _ _ (der_19328 v h) (by intro d hd; cases hd)))
def cl_21921 : CNF.NClause := [(122,true),(49,false),(55,false),(37,true),(57,true)]
theorem der_21921 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21921 :=
  CNF.rup_sound cl_21921 [cl_18182,cl_20396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18182 v h) (hints_cons _ _ _ (der_20396 v h) (by intro d hd; cases hd)))
def cl_21922 : CNF.NClause := [(118,true),(61,false),(33,false),(35,true),(31,true)]
theorem der_21922 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21922 :=
  CNF.rup_sound cl_21922 [cl_14864,cl_15466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14864 v h) (hints_cons _ _ _ (der_15466 v h) (by intro d hd; cases hd)))
def cl_21923 : CNF.NClause := [(87,true),(4,false),(2,false),(1,false),(3,false)]
theorem der_21923 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21923 :=
  CNF.rup_sound cl_21923 [cl_20745,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20745 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_21924 : CNF.NClause := [(64,true),(25,true),(22,false),(12,false),(17,false)]
theorem der_21924 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21924 :=
  CNF.rup_sound cl_21924 [cl_21599,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21599 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_21925 : CNF.NClause := [(69,true),(9,true),(11,false),(20,true),(2,false)]
theorem der_21925 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21925 :=
  CNF.rup_sound cl_21925 [cl_20731,cl_17996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20731 v h) (hints_cons _ _ _ (der_17996 v h) (by intro d hd; cases hd)))
def cl_21926 : CNF.NClause := [(117,true),(60,false),(49,false),(36,true),(53,true)]
theorem der_21926 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21926 :=
  CNF.rup_sound cl_21926 [cl_18678,cl_18288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18678 v h) (hints_cons _ _ _ (der_18288 v h) (by intro d hd; cases hd)))
def cl_21927 : CNF.NClause := [(111,true),(34,true),(38,true),(55,false),(46,false)]
theorem der_21927 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21927 :=
  CNF.rup_sound cl_21927 [cl_19605,cl_18676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19605 v h) (hints_cons _ _ _ (der_18676 v h) (by intro d hd; cases hd)))
def cl_21928 : CNF.NClause := [(120,true),(31,false),(45,false),(38,true),(47,true)]
theorem der_21928 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21928 :=
  CNF.rup_sound cl_21928 [cl_20169,cl_20001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20169 v h) (hints_cons _ _ _ (der_20001 v h) (by intro d hd; cases hd)))
def cl_21929 : CNF.NClause := [(113,true),(36,false),(38,true),(61,false),(37,false)]
theorem der_21929 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21929 :=
  CNF.rup_sound cl_21929 [cl_15469,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15469 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_21930 : CNF.NClause := [(113,true),(36,false),(37,true),(61,false),(39,false)]
theorem der_21930 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21930 :=
  CNF.rup_sound cl_21930 [cl_15476,cl_15474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15476 v h) (hints_cons _ _ _ (der_15474 v h) (by intro d hd; cases hd)))
def cl_21931 : CNF.NClause := [(103,true),(61,false),(42,true),(44,false),(45,false)]
theorem der_21931 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21931 :=
  CNF.rup_sound cl_21931 [cl_15530,cl_15406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15530 v h) (hints_cons _ _ _ (der_15406 v h) (by intro d hd; cases hd)))
def cl_21932 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(57,true)]
theorem der_21932 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21932 :=
  CNF.rup_sound cl_21932 [cl_20004,cl_20396] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20004 v h) (hints_cons _ _ _ (der_20396 v h) (by intro d hd; cases hd)))
def cl_21933 : CNF.NClause := [(101,true),(45,false),(37,true),(48,false),(51,true)]
theorem der_21933 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21933 :=
  CNF.rup_sound cl_21933 [cl_20278,cl_20270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20278 v h) (hints_cons _ _ _ (der_20270 v h) (by intro d hd; cases hd)))
def cl_21934 : CNF.NClause := [(116,true),(36,false),(58,false),(43,false),(52,false)]
theorem der_21934 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21934 :=
  CNF.rup_sound cl_21934 [cl_15239,cl_15173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15239 v h) (hints_cons _ _ _ (der_15173 v h) (by intro d hd; cases hd)))
def cl_21935 : CNF.NClause := [(122,true),(31,false),(55,false),(37,true),(49,false)]
theorem der_21935 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21935 :=
  CNF.rup_sound cl_21935 [cl_19693,cl_19195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19693 v h) (hints_cons _ _ _ (der_19195 v h) (by intro d hd; cases hd)))
def cl_21936 : CNF.NClause := [(70,true),(28,false),(17,false),(6,true),(14,false)]
theorem der_21936 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21936 :=
  CNF.rup_sound cl_21936 [cl_21014,cl_15155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21014 v h) (hints_cons _ _ _ (der_15155 v h) (by intro d hd; cases hd)))
def cl_21937 : CNF.NClause := [(91,true),(6,false),(26,false),(12,false),(18,false)]
theorem der_21937 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21937 :=
  CNF.rup_sound cl_21937 [cl_20492,cl_21867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20492 v h) (hints_cons _ _ _ (der_21867 v h) (by intro d hd; cases hd)))
def cl_21938 : CNF.NClause := [(67,true),(22,false),(30,true),(20,false),(23,false)]
theorem der_21938 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21938 :=
  CNF.rup_sound cl_21938 [cl_20844,cl_18176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20844 v h) (hints_cons _ _ _ (der_18176 v h) (by intro d hd; cases hd)))
def cl_21939 : CNF.NClause := [(77,true),(18,false),(30,true),(16,true),(19,false)]
theorem der_21939 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21939 :=
  CNF.rup_sound cl_21939 [cl_19785,cl_19970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19785 v h) (hints_cons _ _ _ (der_19970 v h) (by intro d hd; cases hd)))
def cl_21940 : CNF.NClause := [(77,true),(16,true),(30,true),(17,false),(15,false)]
theorem der_21940 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21940 :=
  CNF.rup_sound cl_21940 [cl_17790,cl_19970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17790 v h) (hints_cons _ _ _ (der_19970 v h) (by intro d hd; cases hd)))
def cl_21941 : CNF.NClause := [(64,true),(12,false),(7,false),(25,false),(17,false)]
theorem der_21941 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21941 :=
  CNF.rup_sound cl_21941 [cl_21786,cl_21855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21786 v h) (hints_cons _ _ _ (der_21855 v h) (by intro d hd; cases hd)))
def cl_21942 : CNF.NClause := [(90,true),(28,true),(8,false),(11,false),(22,true)]
theorem der_21942 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21942 :=
  CNF.rup_sound cl_21942 [cl_20463,cl_21892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20463 v h) (hints_cons _ _ _ (der_21892 v h) (by intro d hd; cases hd)))
def cl_21943 : CNF.NClause := [(63,true),(14,false),(4,true),(24,false),(19,true)]
theorem der_21943 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21943 :=
  CNF.rup_sound cl_21943 [cl_21452,cl_21327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21452 v h) (hints_cons _ _ _ (der_21327 v h) (by intro d hd; cases hd)))
def cl_21944 : CNF.NClause := [(64,true),(12,false),(17,true),(25,false),(22,false)]
theorem der_21944 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21944 :=
  CNF.rup_sound cl_21944 [cl_21619,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21619 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_21945 : CNF.NClause := [(64,true),(12,false),(25,false),(17,true),(7,false)]
theorem der_21945 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21945 :=
  CNF.rup_sound cl_21945 [cl_21829,cl_21944] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21829 v h) (hints_cons _ _ _ (der_21944 v h) (by intro d hd; cases hd)))
def cl_21946 : CNF.NClause := [(64,true),(17,true),(2,false),(7,false),(12,false)]
theorem der_21946 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21946 :=
  CNF.rup_sound cl_21946 [cl_20766,cl_21945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20766 v h) (hints_cons _ _ _ (der_21945 v h) (by intro d hd; cases hd)))
def cl_21947 : CNF.NClause := [(23,false),(30,true),(21,true),(24,false),(67,true)]
theorem der_21947 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21947 :=
  CNF.rup_sound cl_21947 [cl_20453,cl_18176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20453 v h) (hints_cons _ _ _ (der_18176 v h) (by intro d hd; cases hd)))
def cl_21949 : CNF.NClause := [(18,false),(13,true),(8,true),(65,true),(23,false)]
theorem der_21949 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21949 :=
  CNF.rup_sound cl_21949 [cl_18806,cl_21907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18806 v h) (hints_cons _ _ _ (der_21907 v h) (by intro d hd; cases hd)))
def cl_21950 : CNF.NClause := [(16,false),(24,false),(5,true),(84,true),(13,true)]
theorem der_21950 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21950 :=
  CNF.rup_sound cl_21950 [cl_21592,cl_21780] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21592 v h) (hints_cons _ _ _ (der_21780 v h) (by intro d hd; cases hd)))
def cl_21951 : CNF.NClause := [(80,true),(3,true),(7,true),(24,false),(15,false)]
theorem der_21951 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21951 :=
  CNF.rup_sound cl_21951 [cl_19529,cl_18352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19529 v h) (hints_cons _ _ _ (der_18352 v h) (by intro d hd; cases hd)))
def cl_21952 : CNF.NClause := [(72,true),(13,false),(10,true),(12,false),(30,true)]
theorem der_21952 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21952 :=
  CNF.rup_sound cl_21952 [cl_19519,cl_17632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19519 v h) (hints_cons _ _ _ (der_17632 v h) (by intro d hd; cases hd)))
def cl_21953 : CNF.NClause := [(13,false),(30,false),(14,false),(72,true),(11,true)]
theorem der_21953 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21953 :=
  CNF.rup_sound cl_21953 [cl_15421,cl_15555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15421 v h) (hints_cons _ _ _ (der_15555 v h) (by intro d hd; cases hd)))
def cl_21954 : CNF.NClause := [(64,true),(25,false),(22,false),(12,true),(7,false)]
theorem der_21954 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21954 :=
  CNF.rup_sound cl_21954 [cl_21751,cl_21855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21751 v h) (hints_cons _ _ _ (der_21855 v h) (by intro d hd; cases hd)))
def cl_21955 : CNF.NClause := [(25,true),(64,true),(17,false),(12,true),(22,false)]
theorem der_21955 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21955 :=
  CNF.rup_sound cl_21955 [cl_21711,cl_21894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21711 v h) (hints_cons _ _ _ (der_21894 v h) (by intro d hd; cases hd)))
def cl_21956 : CNF.NClause := [(5,false),(82,true),(6,true),(7,false),(30,false)]
theorem der_21956 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21956 :=
  CNF.rup_sound cl_21956 [cl_15483,cl_15598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15483 v h) (hints_cons _ _ _ (der_15598 v h) (by intro d hd; cases hd)))
def cl_21957 : CNF.NClause := [(91,true),(26,false),(0,true),(24,false),(6,true)]
theorem der_21957 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21957 :=
  CNF.rup_sound cl_21957 [cl_21097,cl_21854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21097 v h) (hints_cons _ _ _ (der_21854 v h) (by intro d hd; cases hd)))
def cl_21959 : CNF.NClause := [(66,true),(1,true),(21,false),(6,true),(25,false)]
theorem der_21959 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21959 :=
  CNF.rup_sound cl_21959 [cl_21818,cl_15538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21818 v h) (hints_cons _ _ _ (der_15538 v h) (by intro d hd; cases hd)))
def cl_21960 : CNF.NClause := [(19,false),(74,true),(6,true),(10,true),(23,false)]
theorem der_21960 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21960 :=
  CNF.rup_sound cl_21960 [cl_20447,cl_15412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20447 v h) (hints_cons _ _ _ (der_15412 v h) (by intro d hd; cases hd)))
def cl_21961 : CNF.NClause := [(78,true),(4,false),(6,true),(15,false),(13,true)]
theorem der_21961 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21961 :=
  CNF.rup_sound cl_21961 [cl_20783,cl_20660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20783 v h) (hints_cons _ _ _ (der_20660 v h) (by intro d hd; cases hd)))
def cl_21962 : CNF.NClause := [(4,false),(78,true),(22,false),(27,true),(15,true)]
theorem der_21962 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21962 :=
  CNF.rup_sound cl_21962 [cl_20433,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20433 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_21963 : CNF.NClause := [(83,true),(26,false),(5,true),(23,false),(4,true)]
theorem der_21963 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21963 :=
  CNF.rup_sound cl_21963 [cl_21827,cl_15548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21827 v h) (hints_cons _ _ _ (der_15548 v h) (by intro d hd; cases hd)))
def cl_21964 : CNF.NClause := [(75,true),(26,false),(16,false),(9,false),(10,true)]
theorem der_21964 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21964 :=
  CNF.rup_sound cl_21964 [cl_21028,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21028 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_21965 : CNF.NClause := [(79,true),(26,false),(8,false),(2,false),(21,false)]
theorem der_21965 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21965 :=
  CNF.rup_sound cl_21965 [cl_20861,cl_20843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20861 v h) (hints_cons _ _ _ (der_20843 v h) (by intro d hd; cases hd)))
def cl_21966 : CNF.NClause := [(79,true),(8,false),(14,false),(15,false),(21,false)]
theorem der_21966 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21966 :=
  CNF.rup_sound cl_21966 [cl_21528,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21528 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_21967 : CNF.NClause := [(79,true),(26,true),(21,false),(8,false),(14,false)]
theorem der_21967 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21967 :=
  CNF.rup_sound cl_21967 [cl_21535,cl_21966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21535 v h) (hints_cons _ _ _ (der_21966 v h) (by intro d hd; cases hd)))
def cl_21969 : CNF.NClause := [(30,false),(5,false),(8,false),(82,true),(7,true)]
theorem der_21969 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21969 :=
  CNF.rup_sound cl_21969 [cl_15473,cl_15595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15473 v h) (hints_cons _ _ _ (der_15595 v h) (by intro d hd; cases hd)))
def cl_21970 : CNF.NClause := [(69,true),(11,true),(9,true),(18,false),(20,false)]
theorem der_21970 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21970 :=
  CNF.rup_sound cl_21970 [cl_19512,cl_15549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19512 v h) (hints_cons _ _ _ (der_15549 v h) (by intro d hd; cases hd)))
def cl_21971 : CNF.NClause := [(64,true),(12,true),(7,false),(25,false),(17,false)]
theorem der_21971 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21971 :=
  CNF.rup_sound cl_21971 [cl_21807,cl_21855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21807 v h) (hints_cons _ _ _ (der_21855 v h) (by intro d hd; cases hd)))
def cl_21972 : CNF.NClause := [(72,true),(11,false),(10,true),(30,true),(14,false)]
theorem der_21972 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21972 :=
  CNF.rup_sound cl_21972 [cl_20298,cl_17632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20298 v h) (hints_cons _ _ _ (der_17632 v h) (by intro d hd; cases hd)))
def cl_21973 : CNF.NClause := [(85,true),(5,false),(27,false),(19,false),(21,false)]
theorem der_21973 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21973 :=
  CNF.rup_sound cl_21973 [cl_15452,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15452 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_21974 : CNF.NClause := [(74,true),(23,false),(29,false),(19,true),(10,true)]
theorem der_21974 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21974 :=
  CNF.rup_sound cl_21974 [cl_20472,cl_21877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20472 v h) (hints_cons _ _ _ (der_21877 v h) (by intro d hd; cases hd)))
def cl_21975 : CNF.NClause := [(119,true),(60,false),(31,false),(40,true),(52,true)]
theorem der_21975 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21975 :=
  CNF.rup_sound cl_21975 [cl_20138,cl_19405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20138 v h) (hints_cons _ _ _ (der_19405 v h) (by intro d hd; cases hd)))
def cl_21976 : CNF.NClause := [(102,true),(50,false),(57,true),(38,true),(32,false)]
theorem der_21976 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21976 :=
  CNF.rup_sound cl_21976 [cl_20216,cl_20352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20216 v h) (hints_cons _ _ _ (der_20352 v h) (by intro d hd; cases hd)))
def cl_21977 : CNF.NClause := [(115,true),(59,false),(36,true),(33,false),(47,true)]
theorem der_21977 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21977 :=
  CNF.rup_sound cl_21977 [cl_18502,cl_18218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18502 v h) (hints_cons _ _ _ (der_18218 v h) (by intro d hd; cases hd)))
def cl_21978 : CNF.NClause := [(95,true),(38,true),(53,false),(56,false),(43,false)]
theorem der_21978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21978 :=
  CNF.rup_sound cl_21978 [cl_20681,cl_15167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20681 v h) (hints_cons _ _ _ (der_15167 v h) (by intro d hd; cases hd)))
def cl_21979 : CNF.NClause := [(95,true),(38,true),(48,true),(43,false),(56,false)]
theorem der_21979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21979 :=
  CNF.rup_sound cl_21979 [cl_20663,cl_21978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20663 v h) (hints_cons _ _ _ (der_21978 v h) (by intro d hd; cases hd)))
def cl_21980 : CNF.NClause := [(95,true),(38,true),(43,false),(33,true),(56,false)]
theorem der_21980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21980 :=
  CNF.rup_sound cl_21980 [cl_20321,cl_21978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20321 v h) (hints_cons _ _ _ (der_21978 v h) (by intro d hd; cases hd)))
def cl_21981 : CNF.NClause := [(97,true),(32,false),(42,false),(52,true),(37,true)]
theorem der_21981 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21981 :=
  CNF.rup_sound cl_21981 [cl_20217,cl_20687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20217 v h) (hints_cons _ _ _ (der_20687 v h) (by intro d hd; cases hd)))
def cl_21982 : CNF.NClause := [(65,true),(3,true),(25,false),(18,false),(23,false)]
theorem der_21982 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21982 :=
  CNF.rup_sound cl_21982 [cl_20617,cl_19422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20617 v h) (hints_cons _ _ _ (der_19422 v h) (by intro d hd; cases hd)))
def cl_21983 : CNF.NClause := [(65,true),(18,false),(3,true),(8,false),(25,false)]
theorem der_21983 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21983 :=
  CNF.rup_sound cl_21983 [cl_20502,cl_21982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20502 v h) (hints_cons _ _ _ (der_21982 v h) (by intro d hd; cases hd)))
def cl_21985 : CNF.NClause := [(6,false),(26,true),(24,false),(91,true),(18,true)]
theorem der_21985 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21985 :=
  CNF.rup_sound cl_21985 [cl_19912,cl_19858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19912 v h) (hints_cons _ _ _ (der_19858 v h) (by intro d hd; cases hd)))
def cl_21986 : CNF.NClause := [(90,true),(8,true),(11,true),(19,false),(22,false)]
theorem der_21986 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21986 :=
  CNF.rup_sound cl_21986 [cl_19632,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19632 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_21987 : CNF.NClause := [(90,true),(8,false),(0,true),(19,true),(22,false)]
theorem der_21987 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21987 :=
  CNF.rup_sound cl_21987 [cl_21566,cl_20427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21566 v h) (hints_cons _ _ _ (der_20427 v h) (by intro d hd; cases hd)))
def cl_21988 : CNF.NClause := [(80,true),(29,true),(7,false),(11,false),(24,true)]
theorem der_21988 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21988 :=
  CNF.rup_sound cl_21988 [cl_21041,cl_21016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21041 v h) (hints_cons _ _ _ (der_21016 v h) (by intro d hd; cases hd)))
def cl_21989 : CNF.NClause := [(102,true),(44,false),(57,true),(38,true),(32,false)]
theorem der_21989 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21989 :=
  CNF.rup_sound cl_21989 [cl_18479,cl_21976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18479 v h) (hints_cons _ _ _ (der_21976 v h) (by intro d hd; cases hd)))
def cl_21991 : CNF.NClause := [(103,true),(41,false),(44,false),(45,false),(43,false)]
theorem der_21991 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21991 :=
  CNF.rup_sound cl_21991 [cl_15163,cl_15406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15163 v h) (hints_cons _ _ _ (der_15406 v h) (by intro d hd; cases hd)))
def cl_21992 : CNF.NClause := [(103,true),(44,false),(41,true),(43,false),(45,false)]
theorem der_21992 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21992 :=
  CNF.rup_sound cl_21992 [cl_15235,cl_15406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15235 v h) (hints_cons _ _ _ (der_15406 v h) (by intro d hd; cases hd)))
def cl_21993 : CNF.NClause := [(99,true),(60,false),(51,false),(43,false),(47,false)]
theorem der_21993 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21993 :=
  CNF.rup_sound cl_21993 [cl_15162,cl_14913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15162 v h) (hints_cons _ _ _ (der_14913 v h) (by intro d hd; cases hd)))
def cl_21994 : CNF.NClause := [(112,true),(43,false),(46,false),(40,false),(59,false)]
theorem der_21994 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21994 :=
  CNF.rup_sound cl_21994 [cl_14905,cl_15238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_14905 v h) (hints_cons _ _ _ (der_15238 v h) (by intro d hd; cases hd)))
def cl_21995 : CNF.NClause := [(112,true),(43,false),(46,false),(54,false),(40,true)]
theorem der_21995 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21995 :=
  CNF.rup_sound cl_21995 [cl_15170,cl_20324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15170 v h) (hints_cons _ _ _ (der_20324 v h) (by intro d hd; cases hd)))
def cl_21996 : CNF.NClause := [(108,true),(49,false),(48,false),(61,true),(47,true)]
theorem der_21996 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21996 :=
  CNF.rup_sound cl_21996 [cl_19525,cl_19986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19525 v h) (hints_cons _ _ _ (der_19986 v h) (by intro d hd; cases hd)))
def cl_21997 : CNF.NClause := [(110,true),(52,true),(45,false),(33,false),(57,true)]
theorem der_21997 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21997 :=
  CNF.rup_sound cl_21997 [cl_20280,cl_20271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20280 v h) (hints_cons _ _ _ (der_20271 v h) (by intro d hd; cases hd)))
def cl_21998 : CNF.NClause := [(60,false),(111,true),(42,false),(34,true),(38,true)]
theorem der_21998 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21998 :=
  CNF.rup_sound cl_21998 [cl_18118,cl_18676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18118 v h) (hints_cons _ _ _ (der_18676 v h) (by intro d hd; cases hd)))
def cl_21999 : CNF.NClause := [(99,true),(51,false),(47,false),(43,false),(39,false)]
theorem der_21999 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_21999 :=
  CNF.rup_sound cl_21999 [cl_15237,cl_14913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15237 v h) (hints_cons _ _ _ (der_14913 v h) (by intro d hd; cases hd)))
def cl_22000 : CNF.NClause := [(108,true),(49,false),(61,true),(46,false),(47,true)]
theorem der_22000 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22000 :=
  CNF.rup_sound cl_22000 [cl_18948,cl_21996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18948 v h) (hints_cons _ _ _ (der_21996 v h) (by intro d hd; cases hd)))
def cl_22001 : CNF.NClause := [(108,true),(50,false),(46,false),(61,true),(47,true)]
theorem der_22001 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22001 :=
  CNF.rup_sound cl_22001 [cl_20317,cl_19986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20317 v h) (hints_cons _ _ _ (der_19986 v h) (by intro d hd; cases hd)))
def cl_22003 : CNF.NClause := [(61,false),(118,true),(32,false),(34,true),(31,true)]
theorem der_22003 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22003 :=
  CNF.rup_sound cl_22003 [cl_15535,cl_15465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15535 v h) (hints_cons _ _ _ (der_15465 v h) (by intro d hd; cases hd)))
def cl_22005 : CNF.NClause := [(112,true),(46,false),(43,true),(32,true),(59,false)]
theorem der_22005 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22005 :=
  CNF.rup_sound cl_22005 [cl_18865,cl_17958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18865 v h) (hints_cons _ _ _ (der_17958 v h) (by intro d hd; cases hd)))
def cl_22006 : CNF.NClause := [(75,true),(26,false),(22,false),(10,true),(9,true)]
theorem der_22006 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22006 :=
  CNF.rup_sound cl_22006 [cl_17645,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17645 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_22007 : CNF.NClause := [(75,true),(22,false),(16,false),(9,true),(10,true)]
theorem der_22007 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22007 :=
  CNF.rup_sound cl_22007 [cl_18708,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18708 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_22008 : CNF.NClause := [(96,true),(44,false),(39,true),(56,false),(49,false)]
theorem der_22008 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22008 :=
  CNF.rup_sound cl_22008 [cl_15136,cl_18681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15136 v h) (hints_cons _ _ _ (der_18681 v h) (by intro d hd; cases hd)))
def cl_22009 : CNF.NClause := [(118,true),(32,false),(33,true),(34,true),(35,false)]
theorem der_22009 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22009 :=
  CNF.rup_sound cl_22009 [cl_18554,cl_15536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18554 v h) (hints_cons _ _ _ (der_15536 v h) (by intro d hd; cases hd)))
def cl_22010 : CNF.NClause := [(119,true),(44,false),(31,false),(40,true),(52,true)]
theorem der_22010 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22010 :=
  CNF.rup_sound cl_22010 [cl_18610,cl_19405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18610 v h) (hints_cons _ _ _ (der_19405 v h) (by intro d hd; cases hd)))
def cl_22011 : CNF.NClause := [(94,true),(40,true),(56,false),(55,false),(50,true)]
theorem der_22011 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22011 :=
  CNF.rup_sound cl_22011 [cl_18382,cl_20267] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18382 v h) (hints_cons _ _ _ (der_20267 v h) (by intro d hd; cases hd)))
def cl_22012 : CNF.NClause := [(100,true),(49,false),(58,true),(33,false),(40,true)]
theorem der_22012 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22012 :=
  CNF.rup_sound cl_22012 [cl_18277,cl_18879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18277 v h) (hints_cons _ _ _ (der_18879 v h) (by intro d hd; cases hd)))
def cl_22013 : CNF.NClause := [(100,true),(40,true),(58,true),(42,false),(33,false)]
theorem der_22013 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22013 :=
  CNF.rup_sound cl_22013 [cl_18470,cl_18879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18470 v h) (hints_cons _ _ _ (der_18879 v h) (by intro d hd; cases hd)))
def cl_22014 : CNF.NClause := [(112,true),(32,false),(40,true),(54,false),(46,false)]
theorem der_22014 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22014 :=
  CNF.rup_sound cl_22014 [cl_19225,cl_21995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19225 v h) (hints_cons _ _ _ (der_21995 v h) (by intro d hd; cases hd)))
def cl_22015 : CNF.NClause := [(112,true),(43,false),(46,false),(40,true),(32,true)]
theorem der_22015 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22015 :=
  CNF.rup_sound cl_22015 [cl_20383,cl_21995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20383 v h) (hints_cons _ _ _ (der_21995 v h) (by intro d hd; cases hd)))
def cl_22016 : CNF.NClause := [(73,true),(28,false),(18,false),(10,true),(7,true)]
theorem der_22016 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22016 :=
  CNF.rup_sound cl_22016 [cl_18136,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18136 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22017 : CNF.NClause := [(77,true),(18,false),(17,false),(16,true),(30,true)]
theorem der_22017 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22017 :=
  CNF.rup_sound cl_22017 [cl_18691,cl_19970] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18691 v h) (hints_cons _ _ _ (der_19970 v h) (by intro d hd; cases hd)))
def cl_22018 : CNF.NClause := [(285,false),(10,true),(74,true),(5,true),(19,true)]
theorem der_22018 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22018 :=
  CNF.rup_sound cl_22018 [cl_18800,cl_13921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18800 v h) (hints_cons _ _ _ (inp_13921 v h) (by intro d hd; cases hd)))
def cl_22019 : CNF.NClause := [(91,true),(12,false),(18,false),(0,true),(6,false)]
theorem der_22019 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22019 :=
  CNF.rup_sound cl_22019 [cl_18127,cl_21937] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18127 v h) (hints_cons _ _ _ (der_21937 v h) (by intro d hd; cases hd)))
def cl_22020 : CNF.NClause := [(92,true),(20,false),(15,false),(5,true),(10,true)]
theorem der_22020 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22020 :=
  CNF.rup_sound cl_22020 [cl_17696,cl_19353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17696 v h) (hints_cons _ _ _ (der_19353 v h) (by intro d hd; cases hd)))
def cl_22022 : CNF.NClause := [(425,false),(9,true),(21,true),(67,true),(30,true)]
theorem der_22022 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22022 :=
  CNF.rup_sound cl_22022 [cl_18433,cl_14057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18433 v h) (hints_cons _ _ _ (inp_14057 v h) (by intro d hd; cases hd)))
def cl_22023 : CNF.NClause := [(84,true),(2,true),(13,false),(28,false),(5,true)]
theorem der_22023 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22023 :=
  CNF.rup_sound cl_22023 [cl_18564,cl_21913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18564 v h) (hints_cons _ _ _ (der_21913 v h) (by intro d hd; cases hd)))
def cl_22024 : CNF.NClause := [(92,true),(25,false),(15,false),(10,true),(5,true)]
theorem der_22024 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22024 :=
  CNF.rup_sound cl_22024 [cl_18270,cl_18055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18270 v h) (hints_cons _ _ _ (der_18055 v h) (by intro d hd; cases hd)))
def cl_22026 : CNF.NClause := [(63,true),(9,true),(14,true),(24,false),(25,false)]
theorem der_22026 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22026 :=
  CNF.rup_sound cl_22026 [cl_18546,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18546 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_22027 : CNF.NClause := [(111,true),(38,true),(55,false),(42,false),(34,true)]
theorem der_22027 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22027 :=
  CNF.rup_sound cl_22027 [cl_18381,cl_18676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18381 v h) (hints_cons _ _ _ (der_18676 v h) (by intro d hd; cases hd)))
def cl_22028 : CNF.NClause := [(123,true),(46,false),(56,false),(41,true),(36,true)]
theorem der_22028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22028 :=
  CNF.rup_sound cl_22028 [cl_18861,cl_19240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18861 v h) (hints_cons _ _ _ (der_19240 v h) (by intro d hd; cases hd)))
def cl_22029 : CNF.NClause := [(67,true),(21,true),(22,false),(20,false),(30,true)]
theorem der_22029 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22029 :=
  CNF.rup_sound cl_22029 [cl_18105,cl_21938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18105 v h) (hints_cons _ _ _ (der_21938 v h) (by intro d hd; cases hd)))
def cl_22031 : CNF.NClause := [(84,true),(28,false),(13,false),(2,false),(5,true)]
theorem der_22031 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22031 :=
  CNF.rup_sound cl_22031 [cl_18101,cl_21913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18101 v h) (hints_cons _ _ _ (der_21913 v h) (by intro d hd; cases hd)))
def cl_22032 : CNF.NClause := [(29,false),(13,false),(88,true),(21,true),(9,true)]
theorem der_22032 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22032 :=
  CNF.rup_sound cl_22032 [cl_18412,cl_18164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18412 v h) (hints_cons _ _ _ (der_18164 v h) (by intro d hd; cases hd)))
def cl_22033 : CNF.NClause := [(92,true),(20,false),(25,false),(10,true),(5,true)]
theorem der_22033 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22033 :=
  CNF.rup_sound cl_22033 [cl_18878,cl_22020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18878 v h) (hints_cons _ _ _ (der_22020 v h) (by intro d hd; cases hd)))
def cl_22034 : CNF.NClause := [(87,true),(3,true),(0,false),(2,false),(30,true)]
theorem der_22034 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22034 :=
  CNF.rup_sound cl_22034 [cl_17910,cl_21853] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17910 v h) (hints_cons _ _ _ (der_21853 v h) (by intro d hd; cases hd)))
def cl_22035 : CNF.NClause := [(115,true),(44,false),(47,true),(33,false),(59,false)]
theorem der_22035 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22035 :=
  CNF.rup_sound cl_22035 [cl_18229,cl_18264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18229 v h) (hints_cons _ _ _ (der_18264 v h) (by intro d hd; cases hd)))
def cl_22036 : CNF.NClause := [(81,true),(9,true),(1,false),(23,false),(15,false)]
theorem der_22036 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22036 :=
  CNF.rup_sound cl_22036 [cl_19664,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19664 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22038 : CNF.NClause := [(77,true),(18,false),(15,false),(30,true),(16,true)]
theorem der_22038 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22038 :=
  CNF.rup_sound cl_22038 [cl_19580,cl_21939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19580 v h) (hints_cons _ _ _ (der_21939 v h) (by intro d hd; cases hd)))
def cl_22039 : CNF.NClause := [(65,true),(18,false),(25,false),(8,true),(3,true)]
theorem der_22039 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22039 :=
  CNF.rup_sound cl_22039 [cl_20167,cl_19422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20167 v h) (hints_cons _ _ _ (der_19422 v h) (by intro d hd; cases hd)))
def cl_22040 : CNF.NClause := [(100,true),(49,false),(51,false),(58,true),(40,true)]
theorem der_22040 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22040 :=
  CNF.rup_sound cl_22040 [cl_20123,cl_18879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20123 v h) (hints_cons _ _ _ (der_18879 v h) (by intro d hd; cases hd)))
def cl_22041 : CNF.NClause := [(84,true),(16,true),(24,false),(13,false),(5,true)]
theorem der_22041 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22041 :=
  CNF.rup_sound cl_22041 [cl_19255,cl_21911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19255 v h) (hints_cons _ _ _ (der_21911 v h) (by intro d hd; cases hd)))
def cl_22042 : CNF.NClause := [(76,true),(17,false),(24,false),(10,true),(8,true)]
theorem der_22042 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22042 :=
  CNF.rup_sound cl_22042 [cl_19460,cl_15415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19460 v h) (hints_cons _ _ _ (der_15415 v h) (by intro d hd; cases hd)))
def cl_22043 : CNF.NClause := [(80,true),(3,true),(29,false),(24,false),(7,true)]
theorem der_22043 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22043 :=
  CNF.rup_sound cl_22043 [cl_19783,cl_17683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19783 v h) (hints_cons _ _ _ (der_17683 v h) (by intro d hd; cases hd)))
def cl_22044 : CNF.NClause := [(63,true),(19,false),(4,false),(24,false),(9,true)]
theorem der_22044 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22044 :=
  CNF.rup_sound cl_22044 [cl_19702,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19702 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_22045 : CNF.NClause := [(72,true),(14,false),(12,false),(30,true),(10,true)]
theorem der_22045 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22045 :=
  CNF.rup_sound cl_22045 [cl_19692,cl_17632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19692 v h) (hints_cons _ _ _ (der_17632 v h) (by intro d hd; cases hd)))
def cl_22046 : CNF.NClause := [(13,false),(7,true),(71,true),(20,false),(26,true)]
theorem der_22046 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22046 :=
  CNF.rup_sound cl_22046 [cl_19170,cl_19891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19170 v h) (hints_cons _ _ _ (der_19891 v h) (by intro d hd; cases hd)))
def cl_22049 : CNF.NClause := [(453,true),(23,true),(19,false),(74,true),(10,true)]
theorem der_22049 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22049 :=
  CNF.rup_sound cl_22049 [cl_20439,cl_21856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20439 v h) (hints_cons _ _ _ (der_21856 v h) (by intro d hd; cases hd)))
def cl_22050 : CNF.NClause := [(81,true),(9,true),(12,false),(5,true),(291,false)]
theorem der_22050 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22050 :=
  CNF.rup_sound cl_22050 [cl_19172,cl_17623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19172 v h) (hints_cons _ _ _ (der_17623 v h) (by intro d hd; cases hd)))
def cl_22051 : CNF.NClause := [(16,true),(12,false),(68,true),(8,true),(29,false)]
theorem der_22051 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22051 :=
  CNF.rup_sound cl_22051 [cl_19748,cl_19656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19748 v h) (hints_cons _ _ _ (der_19656 v h) (by intro d hd; cases hd)))
def cl_22052 : CNF.NClause := [(80,true),(3,true),(29,false),(15,false),(7,true)]
theorem der_22052 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22052 :=
  CNF.rup_sound cl_22052 [cl_19642,cl_18352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19642 v h) (hints_cons _ _ _ (der_18352 v h) (by intro d hd; cases hd)))
def cl_22053 : CNF.NClause := [(81,true),(23,false),(1,false),(9,true),(28,true)]
theorem der_22053 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22053 :=
  CNF.rup_sound cl_22053 [cl_19782,cl_21870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19782 v h) (hints_cons _ _ _ (der_21870 v h) (by intro d hd; cases hd)))
def cl_22055 : CNF.NClause := [(87,true),(3,true),(4,false),(1058,true),(30,true)]
theorem der_22055 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22055 :=
  CNF.rup_sound cl_22055 [cl_19138,cl_21890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19138 v h) (hints_cons _ _ _ (der_21890 v h) (by intro d hd; cases hd)))
def cl_22057 : CNF.NClause := [(69,true),(2,false),(18,false),(9,true),(27,true)]
theorem der_22057 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22057 :=
  CNF.rup_sound cl_22057 [cl_19687,cl_18018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19687 v h) (hints_cons _ _ _ (der_18018 v h) (by intro d hd; cases hd)))
def cl_22058 : CNF.NClause := [(52,false),(67,false),(85,false),(66,false),(21,true)]
theorem der_22058 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22058 :=
  CNF.rup_sound cl_22058 [cl_20370,cl_20390] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20370 v h) (hints_cons _ _ _ (der_20390 v h) (by intro d hd; cases hd)))
def cl_22059 : CNF.NClause := [(69,true),(9,true),(20,false),(27,true),(11,false)]
theorem der_22059 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22059 :=
  CNF.rup_sound cl_22059 [cl_19133,cl_18018] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19133 v h) (hints_cons _ _ _ (der_18018 v h) (by intro d hd; cases hd)))
def cl_22061 : CNF.NClause := [(68,true),(16,true),(4,false),(20,false),(8,true)]
theorem der_22061 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22061 :=
  CNF.rup_sound cl_22061 [cl_20262,cl_17664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20262 v h) (hints_cons _ _ _ (der_17664 v h) (by intro d hd; cases hd)))
def cl_22062 : CNF.NClause := [(94,true),(45,false),(50,true),(55,false),(40,true)]
theorem der_22062 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22062 :=
  CNF.rup_sound cl_22062 [cl_19162,cl_19973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19162 v h) (hints_cons _ _ _ (der_19973 v h) (by intro d hd; cases hd)))
def cl_22063 : CNF.NClause := [(122,true),(49,false),(55,false),(43,false),(37,true)]
theorem der_22063 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22063 :=
  CNF.rup_sound cl_22063 [cl_19754,cl_15166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19754 v h) (hints_cons _ _ _ (der_15166 v h) (by intro d hd; cases hd)))
def cl_22064 : CNF.NClause := [(94,true),(35,false),(50,true),(40,true),(55,false)]
theorem der_22064 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22064 :=
  CNF.rup_sound cl_22064 [cl_19957,cl_19973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19957 v h) (hints_cons _ _ _ (der_19973 v h) (by intro d hd; cases hd)))
def cl_22065 : CNF.NClause := [(71,true),(7,true),(20,false),(19,false),(26,true)]
theorem der_22065 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22065 :=
  CNF.rup_sound cl_22065 [cl_19851,cl_19891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19851 v h) (hints_cons _ _ _ (der_19891 v h) (by intro d hd; cases hd)))
def cl_22066 : CNF.NClause := [(78,true),(4,false),(6,true),(22,false),(15,false)]
theorem der_22066 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22066 :=
  CNF.rup_sound cl_22066 [cl_20747,cl_21859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20747 v h) (hints_cons _ _ _ (der_21859 v h) (by intro d hd; cases hd)))
def cl_22067 : CNF.NClause := [(80,true),(11,false),(7,true),(24,false),(29,true)]
theorem der_22067 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22067 :=
  CNF.rup_sound cl_22067 [cl_21175,cl_17683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21175 v h) (hints_cons _ _ _ (der_17683 v h) (by intro d hd; cases hd)))
def cl_22068 : CNF.NClause := [(81,true),(28,false),(15,false),(12,false),(1,true)]
theorem der_22068 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22068 :=
  CNF.rup_sound cl_22068 [cl_21556,cl_21886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21556 v h) (hints_cons _ _ _ (der_21886 v h) (by intro d hd; cases hd)))
def cl_22070 : CNF.NClause := [(81,true),(28,true),(9,false),(12,false),(1,true)]
theorem der_22070 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22070 :=
  CNF.rup_sound cl_22070 [cl_21597,cl_21889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21597 v h) (hints_cons _ _ _ (der_21889 v h) (by intro d hd; cases hd)))
def cl_22071 : CNF.NClause := [(83,true),(26,false),(11,false),(5,true),(4,true)]
theorem der_22071 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22071 :=
  CNF.rup_sound cl_22071 [cl_21617,cl_21796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21617 v h) (hints_cons _ _ _ (der_21796 v h) (by intro d hd; cases hd)))
def cl_22073 : CNF.NClause := [(81,true),(28,false),(9,false),(12,true),(1,true)]
theorem der_22073 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22073 :=
  CNF.rup_sound cl_22073 [cl_21708,cl_21885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21708 v h) (hints_cons _ _ _ (der_21885 v h) (by intro d hd; cases hd)))
def cl_22074 : CNF.NClause := [(77,true),(15,false),(19,true),(17,false),(18,false),(30,true)]
theorem der_22074 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22074 :=
  CNF.rup_sound cl_22074 [cl_1009,cl_21940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1009 v h) (hints_cons _ _ _ (der_21940 v h) (by intro d hd; cases hd)))
def cl_22075 : CNF.NClause := [(25,true),(3,true),(13,true),(65,false),(23,true),(8,true)]
theorem der_22075 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22075 :=
  CNF.rup_sound cl_22075 [cl_248,cl_18723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_248 v h) (hints_cons _ _ _ (der_18723 v h) (by intro d hd; cases hd)))
def cl_22076 : CNF.NClause := [(22,false),(21,false),(24,false),(67,true),(20,false),(23,false)]
theorem der_22076 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22076 :=
  CNF.rup_sound cl_22076 [cl_321,cl_21938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_321 v h) (hints_cons _ _ _ (der_21938 v h) (by intro d hd; cases hd)))
def cl_22077 : CNF.NClause := [(92,true),(5,false),(0,false),(10,false),(15,false),(20,false)]
theorem der_22077 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22077 :=
  CNF.rup_sound cl_22077 [cl_1953,cl_15410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1953 v h) (hints_cons _ _ _ (der_15410 v h) (by intro d hd; cases hd)))
def cl_22078 : CNF.NClause := [(71,true),(20,false),(1,false),(13,false),(7,false),(19,false)]
theorem der_22078 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22078 :=
  CNF.rup_sound cl_22078 [cl_609,cl_15179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_609 v h) (hints_cons _ _ _ (der_15179 v h) (by intro d hd; cases hd)))
def cl_22079 : CNF.NClause := [(69,true),(11,false),(2,false),(9,false),(20,false),(18,false)]
theorem der_22079 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22079 :=
  CNF.rup_sound cl_22079 [cl_481,cl_15549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_481 v h) (hints_cons _ _ _ (der_15549 v h) (by intro d hd; cases hd)))
def cl_22080 : CNF.NClause := [(17,false),(3,true),(20,false),(14,false),(70,true),(28,true)]
theorem der_22080 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22080 :=
  CNF.rup_sound cl_22080 [cl_548,cl_21878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_548 v h) (hints_cons _ _ _ (der_21878 v h) (by intro d hd; cases hd)))
def cl_22081 : CNF.NClause := [(70,true),(6,false),(3,false),(14,false),(17,false),(20,false)]
theorem der_22081 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22081 :=
  CNF.rup_sound cl_22081 [cl_545,cl_15155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_545 v h) (hints_cons _ _ _ (der_15155 v h) (by intro d hd; cases hd)))
def cl_22082 : CNF.NClause := [(68,true),(4,false),(16,false),(20,false),(8,false),(12,false)]
theorem der_22082 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22082 :=
  CNF.rup_sound cl_22082 [cl_417,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_417 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22083 : CNF.NClause := [(63,false),(25,true),(19,true),(9,true),(14,true),(4,true)]
theorem der_22083 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22083 :=
  CNF.rup_sound cl_22083 [cl_112,cl_17991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_112 v h) (hints_cons _ _ _ (der_17991 v h) (by intro d hd; cases hd)))
def cl_22084 : CNF.NClause := [(77,true),(18,false),(17,false),(16,false),(15,false),(30,false)]
theorem der_22084 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22084 :=
  CNF.rup_sound cl_22084 [cl_961,cl_977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_961 v h) (hints_cons _ _ _ (inp_977 v h) (by intro d hd; cases hd)))
def cl_22085 : CNF.NClause := [(26,false),(18,false),(0,true),(24,true),(6,true),(91,true)]
theorem der_22085 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22085 :=
  CNF.rup_sound cl_22085 [cl_1880,cl_21869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1880 v h) (hints_cons _ _ _ (der_21869 v h) (by intro d hd; cases hd)))
def cl_22086 : CNF.NClause := [(91,true),(24,false),(12,true),(6,true),(0,true),(18,false)]
theorem der_22086 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22086 :=
  CNF.rup_sound cl_22086 [cl_1896,cl_15482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1896 v h) (hints_cons _ _ _ (der_15482 v h) (by intro d hd; cases hd)))
def cl_22087 : CNF.NClause := [(12,true),(24,true),(91,false),(6,true),(0,true),(26,true)]
theorem der_22087 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22087 :=
  CNF.rup_sound cl_22087 [cl_1912,cl_20803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1912 v h) (hints_cons _ _ _ (der_20803 v h) (by intro d hd; cases hd)))
def cl_22088 : CNF.NClause := [(64,true),(2,true),(12,true),(7,true),(25,false),(17,false)]
theorem der_22088 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22088 :=
  CNF.rup_sound cl_22088 [cl_152,cl_21855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_152 v h) (hints_cons _ _ _ (der_21855 v h) (by intro d hd; cases hd)))
def cl_22089 : CNF.NClause := [(68,true),(16,false),(8,true),(4,true),(12,true),(29,false)]
theorem der_22089 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22089 :=
  CNF.rup_sound cl_22089 [cl_408,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_408 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22090 : CNF.NClause := [(68,true),(16,false),(20,false),(12,true),(8,true),(4,true)]
theorem der_22090 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22090 :=
  CNF.rup_sound cl_22090 [cl_424,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_424 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22091 : CNF.NClause := [(12,true),(68,false),(20,true),(8,true),(29,true),(4,true)]
theorem der_22091 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22091 :=
  CNF.rup_sound cl_22091 [cl_440,cl_19920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_440 v h) (hints_cons _ _ _ (der_19920 v h) (by intro d hd; cases hd)))
def cl_22092 : CNF.NClause := [(81,true),(1,true),(9,false),(12,true),(15,false),(28,false)]
theorem der_22092 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22092 :=
  CNF.rup_sound cl_22092 [cl_1238,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1238 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22093 : CNF.NClause := [(81,true),(23,true),(9,false),(15,false),(1,true),(28,true)]
theorem der_22093 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22093 :=
  CNF.rup_sound cl_22093 [cl_1270,cl_20478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1270 v h) (hints_cons _ _ _ (der_20478 v h) (by intro d hd; cases hd)))
def cl_22094 : CNF.NClause := [(12,true),(30,false),(10,true),(11,true),(13,false),(72,true)]
theorem der_22094 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22094 :=
  CNF.rup_sound cl_22094 [cl_664,cl_15555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_664 v h) (hints_cons _ _ _ (der_15555 v h) (by intro d hd; cases hd)))
def cl_22095 : CNF.NClause := [(72,true),(12,true),(10,true),(14,false),(13,false),(30,true)]
theorem der_22095 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22095 :=
  CNF.rup_sound cl_22095 [cl_680,cl_21095] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_680 v h) (hints_cons _ _ _ (der_21095 v h) (by intro d hd; cases hd)))
def cl_22096 : CNF.NClause := [(72,false),(12,true),(10,true),(14,true),(11,true),(30,true)]
theorem der_22096 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22096 :=
  CNF.rup_sound cl_22096 [cl_696,cl_20025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_696 v h) (hints_cons _ _ _ (der_20025 v h) (by intro d hd; cases hd)))
def cl_22097 : CNF.NClause := [(18,false),(30,false),(16,false),(77,true),(19,false),(15,false)]
theorem der_22097 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22097 :=
  CNF.rup_sound cl_22097 [cl_965,cl_22084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_965 v h) (hints_cons _ _ _ (der_22084 v h) (by intro d hd; cases hd)))
def cl_22098 : CNF.NClause := [(16,false),(77,true),(17,true),(15,false),(18,true),(30,false)]
theorem der_22098 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22098 :=
  CNF.rup_sound cl_22098 [cl_973,cl_20818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_973 v h) (hints_cons _ _ _ (der_20818 v h) (by intro d hd; cases hd)))
def cl_22099 : CNF.NClause := [(77,true),(30,false),(15,false),(16,false),(19,true),(18,false)]
theorem der_22099 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22099 :=
  CNF.rup_sound cl_22099 [cl_981,cl_22084] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_981 v h) (hints_cons _ _ _ (der_22084 v h) (by intro d hd; cases hd)))
def cl_22100 : CNF.NClause := [(18,false),(16,false),(77,true),(17,true),(15,false),(19,false)]
theorem der_22100 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22100 :=
  CNF.rup_sound cl_22100 [cl_997,cl_22097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_997 v h) (hints_cons _ _ _ (der_22097 v h) (by intro d hd; cases hd)))
def cl_22101 : CNF.NClause := [(77,true),(16,false),(17,true),(15,false),(18,true),(30,true)]
theorem der_22101 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22101 :=
  CNF.rup_sound cl_22101 [cl_1005,cl_20818] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1005 v h) (hints_cons _ _ _ (der_20818 v h) (by intro d hd; cases hd)))
def cl_22102 : CNF.NClause := [(77,true),(16,false),(17,true),(15,false),(19,true),(30,true)]
theorem der_22102 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22102 :=
  CNF.rup_sound cl_22102 [cl_1013,cl_22101] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1013 v h) (hints_cons _ _ _ (der_22101 v h) (by intro d hd; cases hd)))
def cl_22103 : CNF.NClause := [(63,false),(14,true),(24,true),(25,true),(9,true),(4,true)]
theorem der_22103 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22103 :=
  CNF.rup_sound cl_22103 [cl_120,cl_17991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_120 v h) (hints_cons _ _ _ (der_17991 v h) (by intro d hd; cases hd)))
def cl_22104 : CNF.NClause := [(66,true),(1,false),(21,false),(6,false),(11,false),(16,false)]
theorem der_22104 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22104 :=
  CNF.rup_sound cl_22104 [cl_289,cl_15538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_289 v h) (hints_cons _ _ _ (der_15538 v h) (by intro d hd; cases hd)))
def cl_22105 : CNF.NClause := [(79,true),(15,false),(21,false),(2,true),(14,false),(8,true)]
theorem der_22105 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22105 :=
  CNF.rup_sound cl_22105 [cl_1124,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1124 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_22106 : CNF.NClause := [(85,true),(5,false),(3,false),(12,false),(19,false),(21,false)]
theorem der_22106 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22106 :=
  CNF.rup_sound cl_22106 [cl_1505,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1505 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22107 : CNF.NClause := [(73,true),(10,false),(7,false),(4,false),(18,false),(21,false)]
theorem der_22107 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22107 :=
  CNF.rup_sound cl_22107 [cl_737,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_737 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22108 : CNF.NClause := [(9,false),(13,false),(88,true),(0,true),(21,false),(17,false)]
theorem der_22108 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22108 :=
  CNF.rup_sound cl_22108 [cl_1698,cl_15419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1698 v h) (hints_cons _ _ _ (der_15419 v h) (by intro d hd; cases hd)))
def cl_22109 : CNF.NClause := [(13,false),(17,false),(9,false),(29,true),(88,true),(21,false)]
theorem der_22109 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22109 :=
  CNF.rup_sound cl_22109 [cl_1697,cl_22108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1697 v h) (hints_cons _ _ _ (der_22108 v h) (by intro d hd; cases hd)))
def cl_22110 : CNF.NClause := [(13,false),(10,false),(11,false),(12,false),(72,true),(14,true)]
theorem der_22110 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22110 :=
  CNF.rup_sound cl_22110 [cl_657,cl_17632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_657 v h) (hints_cons _ _ _ (der_17632 v h) (by intro d hd; cases hd)))
def cl_22111 : CNF.NClause := [(71,true),(7,false),(1,false),(20,false),(13,false),(26,false)]
theorem der_22111 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22111 :=
  CNF.rup_sound cl_22111 [cl_585,cl_15179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_585 v h) (hints_cons _ _ _ (der_15179 v h) (by intro d hd; cases hd)))
def cl_22112 : CNF.NClause := [(71,true),(13,false),(1,false),(20,true),(19,true),(26,false)]
theorem der_22112 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22112 :=
  CNF.rup_sound cl_22112 [cl_601,cl_20668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_601 v h) (hints_cons _ _ _ (der_20668 v h) (by intro d hd; cases hd)))
def cl_22113 : CNF.NClause := [(71,true),(1,false),(20,false),(19,true),(13,false),(26,true)]
theorem der_22113 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22113 :=
  CNF.rup_sound cl_22113 [cl_617,cl_21895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_617 v h) (hints_cons _ _ _ (der_21895 v h) (by intro d hd; cases hd)))
def cl_22114 : CNF.NClause := [(71,true),(13,false),(1,false),(20,true),(19,true),(26,true)]
theorem der_22114 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22114 :=
  CNF.rup_sound cl_22114 [cl_633,cl_21895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_633 v h) (hints_cons _ _ _ (der_21895 v h) (by intro d hd; cases hd)))
def cl_22115 : CNF.NClause := [(21,false),(29,false),(0,true),(9,false),(13,false),(88,true)]
theorem der_22115 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22115 :=
  CNF.rup_sound cl_22115 [cl_1674,cl_15419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1674 v h) (hints_cons _ _ _ (der_15419 v h) (by intro d hd; cases hd)))
def cl_22116 : CNF.NClause := [(29,false),(13,false),(88,true),(0,true),(21,true),(17,true)]
theorem der_22116 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22116 :=
  CNF.rup_sound cl_22116 [cl_1690,cl_22032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1690 v h) (hints_cons _ _ _ (der_22032 v h) (by intro d hd; cases hd)))
def cl_22117 : CNF.NClause := [(9,false),(13,false),(88,true),(0,true),(21,false),(29,true)]
theorem der_22117 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22117 :=
  CNF.rup_sound cl_22117 [cl_1706,cl_22108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1706 v h) (hints_cons _ _ _ (der_22108 v h) (by intro d hd; cases hd)))
def cl_22118 : CNF.NClause := [(9,false),(13,false),(88,true),(29,true),(0,true),(17,true)]
theorem der_22118 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22118 :=
  CNF.rup_sound cl_22118 [cl_1722,cl_22117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1722 v h) (hints_cons _ _ _ (der_22117 v h) (by intro d hd; cases hd)))
def cl_22119 : CNF.NClause := [(21,false),(29,false),(0,false),(9,false),(13,false),(88,true)]
theorem der_22119 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22119 :=
  CNF.rup_sound cl_22119 [cl_1673,cl_15419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1673 v h) (hints_cons _ _ _ (der_15419 v h) (by intro d hd; cases hd)))
def cl_22120 : CNF.NClause := [(29,false),(13,false),(0,false),(88,true),(21,true),(17,true)]
theorem der_22120 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22120 :=
  CNF.rup_sound cl_22120 [cl_1689,cl_22032] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1689 v h) (hints_cons _ _ _ (der_22032 v h) (by intro d hd; cases hd)))
def cl_22121 : CNF.NClause := [(21,false),(0,false),(88,true),(9,false),(13,false),(29,true)]
theorem der_22121 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22121 :=
  CNF.rup_sound cl_22121 [cl_1705,cl_22109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1705 v h) (hints_cons _ _ _ (der_22109 v h) (by intro d hd; cases hd)))
def cl_22122 : CNF.NClause := [(13,false),(88,true),(0,false),(29,true),(21,true),(17,true)]
theorem der_22122 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22122 :=
  CNF.rup_sound cl_22122 [cl_1721,cl_21903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1721 v h) (hints_cons _ _ _ (der_21903 v h) (by intro d hd; cases hd)))
def cl_22123 : CNF.NClause := [(3,true),(8,true),(18,true),(25,true),(65,false),(23,true)]
theorem der_22123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22123 :=
  CNF.rup_sound cl_22123 [cl_252,cl_22075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_252 v h) (hints_cons _ _ _ (der_22075 v h) (by intro d hd; cases hd)))
def cl_22124 : CNF.NClause := [(81,true),(28,false),(9,false),(12,false),(23,false),(1,false)]
theorem der_22124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22124 :=
  CNF.rup_sound cl_22124 [cl_1225,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1225 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22125 : CNF.NClause := [(81,true),(12,true),(28,false),(1,false),(9,false),(23,false)]
theorem der_22125 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22125 :=
  CNF.rup_sound cl_22125 [cl_1229,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1229 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22126 : CNF.NClause := [(81,true),(12,true),(9,true),(28,false),(1,false),(23,false)]
theorem der_22126 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22126 :=
  CNF.rup_sound cl_22126 [cl_1231,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1231 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22127 : CNF.NClause := [(81,true),(28,false),(23,false),(1,true),(12,true),(9,true)]
theorem der_22127 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22127 :=
  CNF.rup_sound cl_22127 [cl_1232,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1232 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22128 : CNF.NClause := [(81,true),(9,false),(28,false),(15,false),(12,false),(1,false)]
theorem der_22128 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22128 :=
  CNF.rup_sound cl_22128 [cl_1233,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1233 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22130 : CNF.NClause := [(81,true),(28,false),(1,false),(15,false),(12,true),(9,false)]
theorem der_22130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22130 :=
  CNF.rup_sound cl_22130 [cl_1237,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1237 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22131 : CNF.NClause := [(81,true),(12,true),(9,true),(1,false),(15,false),(28,false)]
theorem der_22131 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22131 :=
  CNF.rup_sound cl_22131 [cl_1239,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1239 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22132 : CNF.NClause := [(81,true),(9,true),(28,false),(12,true),(1,true),(15,false)]
theorem der_22132 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22132 :=
  CNF.rup_sound cl_22132 [cl_1240,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1240 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22133 : CNF.NClause := [(81,true),(23,true),(15,true),(9,false),(12,false),(28,false)]
theorem der_22133 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22133 :=
  CNF.rup_sound cl_22133 [cl_1241,cl_21884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1241 v h) (hints_cons _ _ _ (der_21884 v h) (by intro d hd; cases hd)))
def cl_22134 : CNF.NClause := [(12,true),(81,true),(1,false),(9,false),(15,true),(28,false)]
theorem der_22134 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22134 :=
  CNF.rup_sound cl_22134 [cl_1245,cl_22125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1245 v h) (hints_cons _ _ _ (der_22125 v h) (by intro d hd; cases hd)))
def cl_22135 : CNF.NClause := [(81,true),(12,true),(9,true),(28,false),(1,false),(23,true)]
theorem der_22135 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22135 :=
  CNF.rup_sound cl_22135 [cl_1247,cl_22131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1247 v h) (hints_cons _ _ _ (der_22131 v h) (by intro d hd; cases hd)))
def cl_22136 : CNF.NClause := [(81,true),(15,false),(9,false),(12,false),(23,false),(1,false)]
theorem der_22136 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22136 :=
  CNF.rup_sound cl_22136 [cl_1249,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1249 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22137 : CNF.NClause := [(81,true),(12,true),(1,false),(15,false),(23,false),(9,false)]
theorem der_22137 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22137 :=
  CNF.rup_sound cl_22137 [cl_1253,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1253 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22139 : CNF.NClause := [(81,true),(1,true),(12,true),(23,false),(15,false),(9,true)]
theorem der_22139 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22139 :=
  CNF.rup_sound cl_22139 [cl_1256,cl_21091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1256 v h) (hints_cons _ _ _ (der_21091 v h) (by intro d hd; cases hd)))
def cl_22140 : CNF.NClause := [(81,true),(28,true),(15,true),(12,false),(23,false),(1,false)]
theorem der_22140 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22140 :=
  CNF.rup_sound cl_22140 [cl_1257,cl_21870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1257 v h) (hints_cons _ _ _ (der_21870 v h) (by intro d hd; cases hd)))
def cl_22141 : CNF.NClause := [(81,true),(28,true),(1,false),(9,false),(15,true),(23,false)]
theorem der_22141 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22141 :=
  CNF.rup_sound cl_22141 [cl_1261,cl_22140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1261 v h) (hints_cons _ _ _ (der_22140 v h) (by intro d hd; cases hd)))
def cl_22142 : CNF.NClause := [(81,true),(1,true),(12,true),(23,false),(15,true),(9,false)]
theorem der_22142 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22142 :=
  CNF.rup_sound cl_22142 [cl_1262,cl_21885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1262 v h) (hints_cons _ _ _ (der_21885 v h) (by intro d hd; cases hd)))
def cl_22144 : CNF.NClause := [(81,true),(12,true),(23,true),(1,false),(9,false),(15,false)]
theorem der_22144 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22144 :=
  CNF.rup_sound cl_22144 [cl_1269,cl_22130] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1269 v h) (hints_cons _ _ _ (der_22130 v h) (by intro d hd; cases hd)))
def cl_22145 : CNF.NClause := [(81,true),(12,true),(9,true),(1,false),(15,false),(28,true)]
theorem der_22145 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22145 :=
  CNF.rup_sound cl_22145 [cl_1271,cl_22036] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1271 v h) (hints_cons _ _ _ (der_22036 v h) (by intro d hd; cases hd)))
def cl_22146 : CNF.NClause := [(81,true),(23,true),(9,false),(12,false),(1,false),(28,true)]
theorem der_22146 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22146 :=
  CNF.rup_sound cl_22146 [cl_1273,cl_20478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1273 v h) (hints_cons _ _ _ (der_20478 v h) (by intro d hd; cases hd)))
def cl_22148 : CNF.NClause := [(12,true),(81,true),(23,true),(1,false),(9,false),(28,true)]
theorem der_22148 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22148 :=
  CNF.rup_sound cl_22148 [cl_1277,cl_22144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1277 v h) (hints_cons _ _ _ (der_22144 v h) (by intro d hd; cases hd)))
def cl_22149 : CNF.NClause := [(12,true),(23,true),(81,false),(9,true),(15,true),(28,true)]
theorem der_22149 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22149 :=
  CNF.rup_sound cl_22149 [cl_1279,cl_20136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1279 v h) (hints_cons _ _ _ (der_20136 v h) (by intro d hd; cases hd)))
def cl_22150 : CNF.NClause := [(87,true),(2,true),(1,false),(0,false),(3,false),(4,false)]
theorem der_22150 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22150 :=
  CNF.rup_sound cl_22150 [cl_1637,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1637 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22151 : CNF.NClause := [(87,true),(0,false),(1,false),(2,true),(3,false),(4,true)]
theorem der_22151 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22151 :=
  CNF.rup_sound cl_22151 [cl_1653,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1653 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22152 : CNF.NClause := [(87,true),(0,false),(4,true),(2,true),(3,true),(1,false)]
theorem der_22152 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22152 :=
  CNF.rup_sound cl_22152 [cl_1661,cl_21852] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1661 v h) (hints_cons _ _ _ (der_21852 v h) (by intro d hd; cases hd)))
def cl_22153 : CNF.NClause := [(76,false),(8,true),(10,true),(27,true),(17,true),(24,true)]
theorem der_22153 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22153 :=
  CNF.rup_sound cl_22153 [cl_959,cl_17896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_959 v h) (hints_cons _ _ _ (der_17896 v h) (by intro d hd; cases hd)))
def cl_22154 : CNF.NClause := [(76,true),(10,false),(1,false),(8,false),(24,false),(17,false)]
theorem der_22154 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22154 :=
  CNF.rup_sound cl_22154 [cl_929,cl_15415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_929 v h) (hints_cons _ _ _ (der_15415 v h) (by intro d hd; cases hd)))
def cl_22155 : CNF.NClause := [(86,true),(22,false),(29,true),(14,false),(18,false),(1,false)]
theorem der_22155 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22155 :=
  CNF.rup_sound cl_22155 [cl_1569,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1569 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22156 : CNF.NClause := [(90,true),(0,false),(8,false),(11,false),(22,false),(19,true)]
theorem der_22156 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22156 :=
  CNF.rup_sound cl_22156 [cl_1801,cl_20427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1801 v h) (hints_cons _ _ _ (der_20427 v h) (by intro d hd; cases hd)))
def cl_22157 : CNF.NClause := [(90,true),(28,false),(0,false),(8,false),(11,false),(19,true)]
theorem der_22157 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22157 :=
  CNF.rup_sound cl_22157 [cl_1817,cl_22156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1817 v h) (hints_cons _ _ _ (der_22156 v h) (by intro d hd; cases hd)))
def cl_22158 : CNF.NClause := [(30,false),(10,false),(12,true),(11,false),(72,true),(14,false)]
theorem der_22158 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22158 :=
  CNF.rup_sound cl_22158 [cl_653,cl_15555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_653 v h) (hints_cons _ _ _ (der_15555 v h) (by intro d hd; cases hd)))
def cl_22159 : CNF.NClause := [(72,true),(30,false),(10,false),(12,true),(13,false),(11,false)]
theorem der_22159 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22159 :=
  CNF.rup_sound cl_22159 [cl_661,cl_15555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_661 v h) (hints_cons _ _ _ (der_15555 v h) (by intro d hd; cases hd)))
def cl_22160 : CNF.NClause := [(30,false),(10,false),(12,true),(11,false),(72,true),(13,true)]
theorem der_22160 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22160 :=
  CNF.rup_sound cl_22160 [cl_669,cl_22158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_669 v h) (hints_cons _ _ _ (der_22158 v h) (by intro d hd; cases hd)))
def cl_22161 : CNF.NClause := [(72,true),(10,false),(11,false),(13,false),(14,false),(30,true)]
theorem der_22161 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22161 :=
  CNF.rup_sound cl_22161 [cl_677,cl_17632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_677 v h) (hints_cons _ _ _ (der_17632 v h) (by intro d hd; cases hd)))
def cl_22162 : CNF.NClause := [(14,false),(10,false),(12,true),(11,false),(72,true),(30,true)]
theorem der_22162 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22162 :=
  CNF.rup_sound cl_22162 [cl_685,cl_22161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_685 v h) (hints_cons _ _ _ (der_22161 v h) (by intro d hd; cases hd)))
def cl_22163 : CNF.NClause := [(10,false),(72,true),(14,true),(13,false),(11,false),(30,true)]
theorem der_22163 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22163 :=
  CNF.rup_sound cl_22163 [cl_693,cl_22110] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_693 v h) (hints_cons _ _ _ (der_22110 v h) (by intro d hd; cases hd)))
def cl_22164 : CNF.NClause := [(10,false),(12,true),(14,true),(11,false),(72,true),(30,true)]
theorem der_22164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22164 :=
  CNF.rup_sound cl_22164 [cl_701,cl_22163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_701 v h) (hints_cons _ _ _ (der_22163 v h) (by intro d hd; cases hd)))
def cl_22165 : CNF.NClause := [(83,true),(4,false),(17,true),(11,false),(26,false),(23,false)]
theorem der_22165 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22165 :=
  CNF.rup_sound cl_22165 [cl_1353,cl_20785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1353 v h) (hints_cons _ _ _ (der_20785 v h) (by intro d hd; cases hd)))
def cl_22166 : CNF.NClause := [(4,false),(17,true),(23,true),(11,false),(83,true),(26,false)]
theorem der_22166 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22166 :=
  CNF.rup_sound cl_22166 [cl_1369,cl_20416] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1369 v h) (hints_cons _ _ _ (der_20416 v h) (by intro d hd; cases hd)))
def cl_22167 : CNF.NClause := [(26,true),(4,false),(17,true),(11,false),(83,true),(23,false)]
theorem der_22167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22167 :=
  CNF.rup_sound cl_22167 [cl_1385,cl_20785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1385 v h) (hints_cons _ _ _ (der_20785 v h) (by intro d hd; cases hd)))
def cl_22168 : CNF.NClause := [(5,false),(4,false),(17,true),(23,true),(11,false),(83,true)]
theorem der_22168 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22168 :=
  CNF.rup_sound cl_22168 [cl_1401,cl_22166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1401 v h) (hints_cons _ _ _ (der_22166 v h) (by intro d hd; cases hd)))
def cl_22169 : CNF.NClause := [(27,false),(2,true),(20,false),(9,false),(11,false),(69,true)]
theorem der_22169 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22169 :=
  CNF.rup_sound cl_22169 [cl_458,cl_15549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_458 v h) (hints_cons _ _ _ (der_15549 v h) (by intro d hd; cases hd)))
def cl_22170 : CNF.NClause := [(27,false),(2,true),(18,true),(9,false),(11,false),(69,true)]
theorem der_22170 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22170 :=
  CNF.rup_sound cl_22170 [cl_474,cl_22169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_474 v h) (hints_cons _ _ _ (der_22169 v h) (by intro d hd; cases hd)))
def cl_22171 : CNF.NClause := [(69,true),(9,false),(2,true),(20,false),(11,false),(18,true)]
theorem der_22171 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22171 :=
  CNF.rup_sound cl_22171 [cl_490,cl_22169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_490 v h) (hints_cons _ _ _ (der_22169 v h) (by intro d hd; cases hd)))
def cl_22172 : CNF.NClause := [(27,false),(11,false),(20,false),(9,false),(69,true),(18,true)]
theorem der_22172 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22172 :=
  CNF.rup_sound cl_22172 [cl_457,cl_22169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_457 v h) (hints_cons _ _ _ (der_22169 v h) (by intro d hd; cases hd)))
def cl_22173 : CNF.NClause := [(27,false),(11,false),(18,true),(9,false),(69,true),(20,true)]
theorem der_22173 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22173 :=
  CNF.rup_sound cl_22173 [cl_473,cl_22170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_473 v h) (hints_cons _ _ _ (der_22170 v h) (by intro d hd; cases hd)))
def cl_22174 : CNF.NClause := [(69,true),(9,false),(27,true),(11,false),(20,false),(18,true)]
theorem der_22174 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22174 :=
  CNF.rup_sound cl_22174 [cl_489,cl_22171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_489 v h) (hints_cons _ _ _ (der_22171 v h) (by intro d hd; cases hd)))
def cl_22175 : CNF.NClause := [(30,false),(13,false),(10,true),(11,false),(72,true),(14,false)]
theorem der_22175 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22175 :=
  CNF.rup_sound cl_22175 [cl_642,cl_15555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_642 v h) (hints_cons _ _ _ (der_15555 v h) (by intro d hd; cases hd)))
def cl_22176 : CNF.NClause := [(66,true),(11,false),(1,false),(6,true),(21,false),(25,false)]
theorem der_22176 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22176 :=
  CNF.rup_sound cl_22176 [cl_267,cl_15538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_267 v h) (hints_cons _ _ _ (der_15538 v h) (by intro d hd; cases hd)))
def cl_22177 : CNF.NClause := [(66,true),(1,false),(21,false),(6,true),(11,false),(16,false)]
theorem der_22177 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22177 :=
  CNF.rup_sound cl_22177 [cl_291,cl_15538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_291 v h) (hints_cons _ _ _ (der_15538 v h) (by intro d hd; cases hd)))
def cl_22178 : CNF.NClause := [(66,true),(11,false),(1,false),(6,true),(16,true),(21,false)]
theorem der_22178 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22178 :=
  CNF.rup_sound cl_22178 [cl_299,cl_22176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_299 v h) (hints_cons _ _ _ (der_22176 v h) (by intro d hd; cases hd)))
def cl_22179 : CNF.NClause := [(66,true),(1,false),(6,true),(11,false),(21,true),(25,true)]
theorem der_22179 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22179 :=
  CNF.rup_sound cl_22179 [cl_315,cl_20717] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_315 v h) (hints_cons _ _ _ (der_20717 v h) (by intro d hd; cases hd)))
def cl_22180 : CNF.NClause := [(14,true),(89,false),(0,true),(23,true),(7,true),(27,true)]
theorem der_22180 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22180 :=
  CNF.rup_sound cl_22180 [cl_1784,cl_18273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1784 v h) (hints_cons _ _ _ (der_18273 v h) (by intro d hd; cases hd)))
def cl_22181 : CNF.NClause := [(7,true),(71,true),(13,false),(19,false),(1,true),(26,false)]
theorem der_22181 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22181 :=
  CNF.rup_sound cl_22181 [cl_596,cl_15179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_596 v h) (hints_cons _ _ _ (der_15179 v h) (by intro d hd; cases hd)))
def cl_22183 : CNF.NClause := [(71,true),(13,false),(20,false),(7,true),(26,true),(19,true)]
theorem der_22183 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22183 :=
  CNF.rup_sound cl_22183 [cl_620,cl_21895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_620 v h) (hints_cons _ _ _ (der_21895 v h) (by intro d hd; cases hd)))
def cl_22184 : CNF.NClause := [(71,true),(13,false),(1,true),(19,false),(7,true),(26,true)]
theorem der_22184 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22184 :=
  CNF.rup_sound cl_22184 [cl_628,cl_22065] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_628 v h) (hints_cons _ _ _ (der_22065 v h) (by intro d hd; cases hd)))
def cl_22185 : CNF.NClause := [(1,true),(20,true),(71,false),(7,true),(19,true),(26,true)]
theorem der_22185 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22185 :=
  CNF.rup_sound cl_22185 [cl_636,cl_19243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_636 v h) (hints_cons _ _ _ (der_19243 v h) (by intro d hd; cases hd)))
def cl_22186 : CNF.NClause := [(64,true),(12,false),(17,false),(2,true),(7,true),(25,false)]
theorem der_22186 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22186 :=
  CNF.rup_sound cl_22186 [cl_148,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_148 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_22187 : CNF.NClause := [(64,true),(17,true),(25,false),(7,true),(2,true),(12,false)]
theorem der_22187 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22187 :=
  CNF.rup_sound cl_22187 [cl_156,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_156 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_22188 : CNF.NClause := [(64,true),(17,false),(2,true),(12,false),(25,true),(7,true)]
theorem der_22188 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22188 :=
  CNF.rup_sound cl_22188 [cl_180,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_180 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_22189 : CNF.NClause := [(80,true),(3,true),(11,false),(7,true),(24,true),(29,false)]
theorem der_22189 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22189 :=
  CNF.rup_sound cl_22189 [cl_1180,cl_18352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1180 v h) (hints_cons _ _ _ (der_18352 v h) (by intro d hd; cases hd)))
def cl_22190 : CNF.NClause := [(73,true),(10,false),(4,true),(28,false),(7,true),(21,false)]
theorem der_22190 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22190 :=
  CNF.rup_sound cl_22190 [cl_716,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_716 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22191 : CNF.NClause := [(73,true),(18,false),(4,true),(28,false),(10,false),(7,true)]
theorem der_22191 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22191 :=
  CNF.rup_sound cl_22191 [cl_724,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_724 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22192 : CNF.NClause := [(73,true),(10,false),(4,true),(28,false),(7,true),(18,true)]
theorem der_22192 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22192 :=
  CNF.rup_sound cl_22192 [cl_732,cl_22190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_732 v h) (hints_cons _ _ _ (der_22190 v h) (by intro d hd; cases hd)))
def cl_22193 : CNF.NClause := [(73,true),(18,false),(4,true),(10,false),(21,false),(7,true)]
theorem der_22193 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22193 :=
  CNF.rup_sound cl_22193 [cl_740,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_740 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22194 : CNF.NClause := [(73,true),(10,false),(4,true),(7,true),(18,true),(21,false)]
theorem der_22194 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22194 :=
  CNF.rup_sound cl_22194 [cl_748,cl_22190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_748 v h) (hints_cons _ _ _ (der_22190 v h) (by intro d hd; cases hd)))
def cl_22195 : CNF.NClause := [(73,true),(18,false),(4,true),(10,false),(7,true),(21,true)]
theorem der_22195 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22195 :=
  CNF.rup_sound cl_22195 [cl_756,cl_22191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_756 v h) (hints_cons _ _ _ (der_22191 v h) (by intro d hd; cases hd)))
def cl_22196 : CNF.NClause := [(21,true),(18,true),(4,true),(7,true),(73,false),(28,true)]
theorem der_22196 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22196 :=
  CNF.rup_sound cl_22196 [cl_764,cl_20016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_764 v h) (hints_cons _ _ _ (der_20016 v h) (by intro d hd; cases hd)))
def cl_22197 : CNF.NClause := [(82,true),(9,false),(8,false),(7,true),(5,true),(6,true)]
theorem der_22197 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22197 :=
  CNF.rup_sound cl_22197 [cl_1320,cl_15598] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1320 v h) (hints_cons _ _ _ (der_15598 v h) (by intro d hd; cases hd)))
def cl_22198 : CNF.NClause := [(21,false),(10,false),(7,true),(73,true),(18,true),(28,false)]
theorem der_22198 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22198 :=
  CNF.rup_sound cl_22198 [cl_715,cl_22194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_715 v h) (hints_cons _ _ _ (der_22194 v h) (by intro d hd; cases hd)))
def cl_22199 : CNF.NClause := [(4,false),(28,false),(73,true),(7,true),(10,true),(18,true)]
theorem der_22199 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22199 :=
  CNF.rup_sound cl_22199 [cl_719,cl_17625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_719 v h) (hints_cons _ _ _ (der_17625 v h) (by intro d hd; cases hd)))
def cl_22200 : CNF.NClause := [(73,true),(18,false),(4,false),(7,true),(10,false),(21,false)]
theorem der_22200 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22200 :=
  CNF.rup_sound cl_22200 [cl_739,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_739 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22201 : CNF.NClause := [(73,true),(4,false),(10,true),(18,false),(21,false),(7,true)]
theorem der_22201 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22201 :=
  CNF.rup_sound cl_22201 [cl_743,cl_15408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_743 v h) (hints_cons _ _ _ (der_15408 v h) (by intro d hd; cases hd)))
def cl_22202 : CNF.NClause := [(73,true),(10,false),(7,true),(18,true),(21,false),(28,true)]
theorem der_22202 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22202 :=
  CNF.rup_sound cl_22202 [cl_747,cl_22194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_747 v h) (hints_cons _ _ _ (der_22194 v h) (by intro d hd; cases hd)))
def cl_22203 : CNF.NClause := [(73,true),(4,false),(10,true),(7,true),(18,true),(21,false)]
theorem der_22203 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22203 :=
  CNF.rup_sound cl_22203 [cl_751,cl_22199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_751 v h) (hints_cons _ _ _ (der_22199 v h) (by intro d hd; cases hd)))
def cl_22204 : CNF.NClause := [(73,true),(18,false),(7,true),(10,false),(21,true),(28,true)]
theorem der_22204 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22204 :=
  CNF.rup_sound cl_22204 [cl_755,cl_22195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_755 v h) (hints_cons _ _ _ (der_22195 v h) (by intro d hd; cases hd)))
def cl_22205 : CNF.NClause := [(73,true),(4,false),(10,true),(18,false),(7,true),(21,true)]
theorem der_22205 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22205 :=
  CNF.rup_sound cl_22205 [cl_759,cl_22016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_759 v h) (hints_cons _ _ _ (der_22016 v h) (by intro d hd; cases hd)))
def cl_22206 : CNF.NClause := [(73,true),(10,false),(4,false),(7,true),(18,true),(21,true)]
theorem der_22206 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22206 :=
  CNF.rup_sound cl_22206 [cl_763,cl_17625] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_763 v h) (hints_cons _ _ _ (der_17625 v h) (by intro d hd; cases hd)))
def cl_22207 : CNF.NClause := [(64,true),(25,true),(7,true),(2,false),(17,true),(22,false)]
theorem der_22207 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22207 :=
  CNF.rup_sound cl_22207 [cl_175,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_175 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_22208 : CNF.NClause := [(64,true),(25,true),(2,false),(7,true),(12,false),(17,false)]
theorem der_22208 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22208 :=
  CNF.rup_sound cl_22208 [cl_179,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_179 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_22209 : CNF.NClause := [(64,true),(17,false),(2,false),(12,true),(25,true),(7,true)]
theorem der_22209 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22209 :=
  CNF.rup_sound cl_22209 [cl_183,cl_21879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_183 v h) (hints_cons _ _ _ (der_21879 v h) (by intro d hd; cases hd)))
def cl_22210 : CNF.NClause := [(64,true),(25,true),(2,false),(7,true),(12,false),(17,true)]
theorem der_22210 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22210 :=
  CNF.rup_sound cl_22210 [cl_187,cl_18786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_187 v h) (hints_cons _ _ _ (der_18786 v h) (by intro d hd; cases hd)))
def cl_22211 : CNF.NClause := [(71,true),(19,false),(26,false),(20,false),(7,true),(1,true)]
theorem der_22211 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22211 :=
  CNF.rup_sound cl_22211 [cl_584,cl_15179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_584 v h) (hints_cons _ _ _ (der_15179 v h) (by intro d hd; cases hd)))
def cl_22212 : CNF.NClause := [(89,true),(14,false),(16,false),(7,true),(23,false),(0,true)]
theorem der_22212 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22212 :=
  CNF.rup_sound cl_22212 [cl_1764,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1764 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22213 : CNF.NClause := [(89,true),(16,false),(0,true),(23,false),(7,true),(27,false)]
theorem der_22213 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22213 :=
  CNF.rup_sound cl_22213 [cl_1736,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1736 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22214 : CNF.NClause := [(71,true),(7,true),(26,false),(20,false),(1,false),(19,false)]
theorem der_22214 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22214 :=
  CNF.rup_sound cl_22214 [cl_583,cl_15179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_583 v h) (hints_cons _ _ _ (der_15179 v h) (by intro d hd; cases hd)))
def cl_22215 : CNF.NClause := [(71,true),(7,true),(26,false),(13,false),(1,false),(19,false)]
theorem der_22215 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22215 :=
  CNF.rup_sound cl_22215 [cl_595,cl_15179] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_595 v h) (hints_cons _ _ _ (der_15179 v h) (by intro d hd; cases hd)))
def cl_22216 : CNF.NClause := [(71,true),(7,true),(26,false),(13,true),(1,false),(20,true)]
theorem der_22216 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22216 :=
  CNF.rup_sound cl_22216 [cl_599,cl_20668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_599 v h) (hints_cons _ _ _ (der_20668 v h) (by intro d hd; cases hd)))
def cl_22217 : CNF.NClause := [(71,true),(1,false),(13,true),(19,true),(7,true),(20,false)]
theorem der_22217 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22217 :=
  CNF.rup_sound cl_22217 [cl_623,cl_20668] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_623 v h) (hints_cons _ _ _ (der_20668 v h) (by intro d hd; cases hd)))
def cl_22218 : CNF.NClause := [(89,true),(16,false),(7,true),(0,false),(23,false),(27,false)]
theorem der_22218 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22218 :=
  CNF.rup_sound cl_22218 [cl_1735,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1735 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22219 : CNF.NClause := [(89,true),(7,true),(0,false),(14,false),(23,false),(27,false)]
theorem der_22219 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22219 :=
  CNF.rup_sound cl_22219 [cl_1739,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1739 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22220 : CNF.NClause := [(89,true),(7,true),(14,true),(0,false),(23,false),(27,false)]
theorem der_22220 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22220 :=
  CNF.rup_sound cl_22220 [cl_1743,cl_22218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1743 v h) (hints_cons _ _ _ (der_22218 v h) (by intro d hd; cases hd)))
def cl_22221 : CNF.NClause := [(89,true),(14,false),(16,false),(7,true),(0,false),(27,false)]
theorem der_22221 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22221 :=
  CNF.rup_sound cl_22221 [cl_1747,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1747 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22222 : CNF.NClause := [(89,true),(7,true),(14,true),(16,false),(23,true),(27,false)]
theorem der_22222 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22222 :=
  CNF.rup_sound cl_22222 [cl_1751,cl_1752] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1751 v h) (hints_cons _ _ _ (inp_1752 v h) (by intro d hd; cases hd)))
def cl_22223 : CNF.NClause := [(89,true),(23,true),(7,true),(0,false),(14,false),(16,true)]
theorem der_22223 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22223 :=
  CNF.rup_sound cl_22223 [cl_1755,cl_17891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1755 v h) (hints_cons _ _ _ (der_17891 v h) (by intro d hd; cases hd)))
def cl_22224 : CNF.NClause := [(89,true),(14,true),(7,true),(27,false),(0,false),(16,true)]
theorem der_22224 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22224 :=
  CNF.rup_sound cl_22224 [cl_1759,cl_22220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1759 v h) (hints_cons _ _ _ (der_22220 v h) (by intro d hd; cases hd)))
def cl_22225 : CNF.NClause := [(89,true),(14,false),(16,false),(7,true),(0,false),(23,false)]
theorem der_22225 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22225 :=
  CNF.rup_sound cl_22225 [cl_1763,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1763 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22227 : CNF.NClause := [(89,true),(7,true),(14,false),(0,false),(23,true),(27,true)]
theorem der_22227 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22227 :=
  CNF.rup_sound cl_22227 [cl_1779,cl_17891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1779 v h) (hints_cons _ _ _ (der_17891 v h) (by intro d hd; cases hd)))
def cl_22228 : CNF.NClause := [(89,true),(16,false),(27,true),(7,true),(14,true),(0,false)]
theorem der_22228 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22228 :=
  CNF.rup_sound cl_22228 [cl_1783,cl_17636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1783 v h) (hints_cons _ _ _ (der_17636 v h) (by intro d hd; cases hd)))
def cl_22229 : CNF.NClause := [(5,false),(9,false),(6,true),(82,true),(8,true),(7,true)]
theorem der_22229 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22229 :=
  CNF.rup_sound cl_22229 [cl_1327,cl_21842] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1327 v h) (hints_cons _ _ _ (der_21842 v h) (by intro d hd; cases hd)))
def cl_22230 : CNF.NClause := [(80,true),(7,true),(29,false),(11,false),(3,false),(24,false)]
theorem der_22230 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22230 :=
  CNF.rup_sound cl_22230 [cl_1163,cl_15488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1163 v h) (hints_cons _ _ _ (der_15488 v h) (by intro d hd; cases hd)))
def cl_22231 : CNF.NClause := [(80,true),(7,true),(3,false),(11,true),(24,false),(29,false)]
theorem der_22231 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22231 :=
  CNF.rup_sound cl_22231 [cl_1167,cl_15488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1167 v h) (hints_cons _ _ _ (der_15488 v h) (by intro d hd; cases hd)))
def cl_22232 : CNF.NClause := [(80,true),(7,true),(11,false),(15,false),(3,false),(29,false)]
theorem der_22232 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22232 :=
  CNF.rup_sound cl_22232 [cl_1171,cl_15488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1171 v h) (hints_cons _ _ _ (der_15488 v h) (by intro d hd; cases hd)))
def cl_22233 : CNF.NClause := [(11,true),(29,false),(7,true),(3,false),(15,false),(80,true)]
theorem der_22233 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22233 :=
  CNF.rup_sound cl_22233 [cl_1175,cl_22231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1175 v h) (hints_cons _ _ _ (der_22231 v h) (by intro d hd; cases hd)))
def cl_22234 : CNF.NClause := [(80,true),(7,true),(11,false),(29,false),(15,true),(24,true)]
theorem der_22234 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22234 :=
  CNF.rup_sound cl_22234 [cl_1179,cl_22189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1179 v h) (hints_cons _ _ _ (der_22189 v h) (by intro d hd; cases hd)))
def cl_22235 : CNF.NClause := [(80,true),(15,true),(7,true),(3,false),(11,true),(29,false)]
theorem der_22235 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22235 :=
  CNF.rup_sound cl_22235 [cl_1183,cl_22231] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1183 v h) (hints_cons _ _ _ (der_22231 v h) (by intro d hd; cases hd)))
def cl_22237 : CNF.NClause := [(80,true),(7,true),(3,false),(15,true),(24,false),(29,true)]
theorem der_22237 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22237 :=
  CNF.rup_sound cl_22237 [cl_1199,cl_22067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1199 v h) (hints_cons _ _ _ (der_22067 v h) (by intro d hd; cases hd)))
def cl_22238 : CNF.NClause := [(80,true),(7,true),(24,true),(3,false),(11,false),(29,true)]
theorem der_22238 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22238 :=
  CNF.rup_sound cl_22238 [cl_1211,cl_20677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1211 v h) (hints_cons _ _ _ (der_20677 v h) (by intro d hd; cases hd)))
def cl_22239 : CNF.NClause := [(6,false),(70,true),(20,false),(14,true),(17,false),(28,false)]
theorem der_22239 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22239 :=
  CNF.rup_sound cl_22239 [cl_517,cl_18578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_517 v h) (hints_cons _ _ _ (der_18578 v h) (by intro d hd; cases hd)))
def cl_22240 : CNF.NClause := [(6,false),(70,true),(3,false),(20,false),(14,true),(28,false)]
theorem der_22240 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22240 :=
  CNF.rup_sound cl_22240 [cl_525,cl_22239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_525 v h) (hints_cons _ _ _ (der_22239 v h) (by intro d hd; cases hd)))
def cl_22241 : CNF.NClause := [(6,false),(17,false),(3,false),(70,true),(14,true),(28,false)]
theorem der_22241 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22241 :=
  CNF.rup_sound cl_22241 [cl_533,cl_22239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_533 v h) (hints_cons _ _ _ (der_22239 v h) (by intro d hd; cases hd)))
def cl_22242 : CNF.NClause := [(6,false),(28,false),(3,false),(70,true),(14,true),(20,true)]
theorem der_22242 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22242 :=
  CNF.rup_sound cl_22242 [cl_541,cl_22241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_541 v h) (hints_cons _ _ _ (der_22241 v h) (by intro d hd; cases hd)))
def cl_22243 : CNF.NClause := [(6,false),(70,true),(3,false),(20,false),(14,true),(17,false)]
theorem der_22243 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22243 :=
  CNF.rup_sound cl_22243 [cl_549,cl_22239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_549 v h) (hints_cons _ _ _ (der_22239 v h) (by intro d hd; cases hd)))
def cl_22244 : CNF.NClause := [(70,true),(3,false),(20,false),(14,true),(17,true),(28,true)]
theorem der_22244 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22244 :=
  CNF.rup_sound cl_22244 [cl_557,cl_20721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_557 v h) (hints_cons _ _ _ (der_20721 v h) (by intro d hd; cases hd)))
def cl_22245 : CNF.NClause := [(6,false),(17,false),(3,false),(70,true),(14,true),(20,true)]
theorem der_22245 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22245 :=
  CNF.rup_sound cl_22245 [cl_565,cl_22241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_565 v h) (hints_cons _ _ _ (der_22241 v h) (by intro d hd; cases hd)))
def cl_22246 : CNF.NClause := [(6,false),(28,true),(3,false),(70,true),(14,true),(17,true)]
theorem der_22246 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22246 :=
  CNF.rup_sound cl_22246 [cl_573,cl_22244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_573 v h) (hints_cons _ _ _ (der_22244 v h) (by intro d hd; cases hd)))
def cl_22247 : CNF.NClause := [(5,false),(6,false),(30,true),(7,true),(9,true),(82,true)]
theorem der_22247 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22247 :=
  CNF.rup_sound cl_22247 [cl_1341,cl_21843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1341 v h) (hints_cons _ _ _ (der_21843 v h) (by intro d hd; cases hd)))
def cl_22248 : CNF.NClause := [(24,false),(12,true),(18,true),(0,false),(91,true),(26,false)]
theorem der_22248 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22248 :=
  CNF.rup_sound cl_22248 [cl_1869,cl_20762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1869 v h) (hints_cons _ _ _ (der_20762 v h) (by intro d hd; cases hd)))
def cl_22249 : CNF.NClause := [(91,true),(12,true),(0,false),(18,false),(6,false),(26,false)]
theorem der_22249 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22249 :=
  CNF.rup_sound cl_22249 [cl_1877,cl_15482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1877 v h) (hints_cons _ _ _ (der_15482 v h) (by intro d hd; cases hd)))
def cl_22250 : CNF.NClause := [(12,true),(6,false),(24,true),(0,false),(91,true),(18,true)]
theorem der_22250 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22250 :=
  CNF.rup_sound cl_22250 [cl_1885,cl_21874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1885 v h) (hints_cons _ _ _ (der_21874 v h) (by intro d hd; cases hd)))
def cl_22252 : CNF.NClause := [(78,true),(6,false),(4,false),(13,true),(22,false),(15,false)]
theorem der_22252 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22252 :=
  CNF.rup_sound cl_22252 [cl_1029,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1029 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22253 : CNF.NClause := [(6,false),(78,true),(4,false),(15,true),(13,true),(22,false)]
theorem der_22253 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22253 :=
  CNF.rup_sound cl_22253 [cl_1037,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1037 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22254 : CNF.NClause := [(78,true),(27,false),(4,false),(13,true),(22,true),(15,false)]
theorem der_22254 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22254 :=
  CNF.rup_sound cl_22254 [cl_1045,cl_21961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1045 v h) (hints_cons _ _ _ (der_21961 v h) (by intro d hd; cases hd)))
def cl_22255 : CNF.NClause := [(6,false),(78,true),(4,false),(15,true),(13,true),(27,false)]
theorem der_22255 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22255 :=
  CNF.rup_sound cl_22255 [cl_1053,cl_22253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1053 v h) (hints_cons _ _ _ (der_22253 v h) (by intro d hd; cases hd)))
def cl_22256 : CNF.NClause := [(78,true),(6,false),(15,false),(13,true),(4,false),(27,true)]
theorem der_22256 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22256 :=
  CNF.rup_sound cl_22256 [cl_1077,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1077 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22257 : CNF.NClause := [(78,true),(6,false),(13,true),(15,true),(4,false),(27,true)]
theorem der_22257 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22257 :=
  CNF.rup_sound cl_22257 [cl_1085,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1085 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22258 : CNF.NClause := [(4,true),(6,false),(78,true),(13,true),(22,false),(15,false)]
theorem der_22258 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22258 :=
  CNF.rup_sound cl_22258 [cl_1030,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1030 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22259 : CNF.NClause := [(4,true),(13,false),(6,false),(78,true),(22,false),(27,false)]
theorem der_22259 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22259 :=
  CNF.rup_sound cl_22259 [cl_1034,cl_15079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1034 v h) (hints_cons _ _ _ (der_15079 v h) (by intro d hd; cases hd)))
def cl_22260 : CNF.NClause := [(4,true),(6,false),(78,true),(15,true),(22,false),(27,false)]
theorem der_22260 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22260 :=
  CNF.rup_sound cl_22260 [cl_1038,cl_22259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1038 v h) (hints_cons _ _ _ (der_22259 v h) (by intro d hd; cases hd)))
def cl_22261 : CNF.NClause := [(4,true),(6,false),(27,false),(78,true),(13,false),(15,false)]
theorem der_22261 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22261 :=
  CNF.rup_sound cl_22261 [cl_1042,cl_22259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1042 v h) (hints_cons _ _ _ (der_22259 v h) (by intro d hd; cases hd)))
def cl_22262 : CNF.NClause := [(4,true),(6,false),(27,false),(78,true),(22,true),(15,false)]
theorem der_22262 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22262 :=
  CNF.rup_sound cl_22262 [cl_1046,cl_22261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1046 v h) (hints_cons _ _ _ (der_22261 v h) (by intro d hd; cases hd)))
def cl_22263 : CNF.NClause := [(4,true),(13,false),(6,false),(78,true),(15,true),(27,false)]
theorem der_22263 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22263 :=
  CNF.rup_sound cl_22263 [cl_1050,cl_22259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1050 v h) (hints_cons _ _ _ (der_22259 v h) (by intro d hd; cases hd)))
def cl_22264 : CNF.NClause := [(4,true),(6,false),(78,true),(15,true),(22,true),(27,false)]
theorem der_22264 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22264 :=
  CNF.rup_sound cl_22264 [cl_1054,cl_22263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1054 v h) (hints_cons _ _ _ (der_22263 v h) (by intro d hd; cases hd)))
def cl_22265 : CNF.NClause := [(78,true),(4,true),(6,false),(13,false),(15,false),(27,true)]
theorem der_22265 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22265 :=
  CNF.rup_sound cl_22265 [cl_1074,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1074 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22266 : CNF.NClause := [(78,true),(4,true),(6,false),(13,true),(15,false),(27,true)]
theorem der_22266 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22266 :=
  CNF.rup_sound cl_22266 [cl_1078,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1078 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22267 : CNF.NClause := [(78,true),(4,true),(15,true),(6,false),(13,false),(27,true)]
theorem der_22267 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22267 :=
  CNF.rup_sound cl_22267 [cl_1082,cl_19297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1082 v h) (hints_cons _ _ _ (der_19297 v h) (by intro d hd; cases hd)))
def cl_22268 : CNF.NClause := [(70,true),(6,false),(14,true),(3,true),(17,true),(20,false)]
theorem der_22268 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22268 :=
  CNF.rup_sound cl_22268 [cl_558,cl_18578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_558 v h) (hints_cons _ _ _ (der_18578 v h) (by intro d hd; cases hd)))
def cl_22269 : CNF.NClause := [(66,true),(1,false),(11,true),(6,false),(21,false),(25,false)]
theorem der_22269 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22269 :=
  CNF.rup_sound cl_22269 [cl_269,cl_15538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_269 v h) (hints_cons _ _ _ (der_15538 v h) (by intro d hd; cases hd)))
def cl_22270 : CNF.NClause := [(11,true),(6,false),(1,false),(66,true),(25,false),(21,true)]
theorem der_22270 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22270 :=
  CNF.rup_sound cl_22270 [cl_277,cl_21896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_277 v h) (hints_cons _ _ _ (der_21896 v h) (by intro d hd; cases hd)))
def cl_22271 : CNF.NClause := [(11,true),(21,false),(1,false),(66,true),(16,false),(6,false)]
theorem der_22271 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22271 :=
  CNF.rup_sound cl_22271 [cl_293,cl_15538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_293 v h) (hints_cons _ _ _ (der_15538 v h) (by intro d hd; cases hd)))
def cl_22272 : CNF.NClause := [(66,true),(16,true),(1,false),(11,true),(6,false),(21,false)]
theorem der_22272 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22272 :=
  CNF.rup_sound cl_22272 [cl_301,cl_22269] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_301 v h) (hints_cons _ _ _ (der_22269 v h) (by intro d hd; cases hd)))
def cl_22273 : CNF.NClause := [(11,true),(6,false),(1,false),(66,true),(16,false),(25,true)]
theorem der_22273 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22273 :=
  CNF.rup_sound cl_22273 [cl_309,cl_22271] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_309 v h) (hints_cons _ _ _ (der_22271 v h) (by intro d hd; cases hd)))
def cl_22274 : CNF.NClause := [(12,true),(8,true),(4,true),(68,false),(29,true),(16,true)]
theorem der_22274 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22274 :=
  CNF.rup_sound cl_22274 [cl_432,cl_19920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_432 v h) (hints_cons _ _ _ (der_19920 v h) (by intro d hd; cases hd)))
def cl_22275 : CNF.NClause := [(68,false),(16,true),(12,true),(20,true),(4,true),(29,true)]
theorem der_22275 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22275 :=
  CNF.rup_sound cl_22275 [cl_446,cl_19920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_446 v h) (hints_cons _ _ _ (der_19920 v h) (by intro d hd; cases hd)))
def cl_22276 : CNF.NClause := [(12,true),(68,false),(8,true),(20,true),(29,true),(16,true)]
theorem der_22276 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22276 :=
  CNF.rup_sound cl_22276 [cl_447,cl_19920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_447 v h) (hints_cons _ _ _ (der_19920 v h) (by intro d hd; cases hd)))
def cl_22277 : CNF.NClause := [(23,true),(83,false),(5,true),(17,true),(11,true),(26,true)]
theorem der_22277 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22277 :=
  CNF.rup_sound cl_22277 [cl_1407,cl_19541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1407 v h) (hints_cons _ _ _ (der_19541 v h) (by intro d hd; cases hd)))
def cl_22278 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,false),(4,false)]
theorem der_22278 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22278 :=
  CNF.rup_sound cl_22278 [cl_1635,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1635 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22279 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,false),(4,false)]
theorem der_22279 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22279 :=
  CNF.rup_sound cl_22279 [cl_1639,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1639 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22280 : CNF.NClause := [(87,true),(2,true),(4,false),(1,false),(0,true),(3,false)]
theorem der_22280 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22280 :=
  CNF.rup_sound cl_22280 [cl_1638,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1638 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22281 : CNF.NClause := [(22,true),(6,true),(13,true),(15,true),(78,false),(27,true)]
theorem der_22281 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22281 :=
  CNF.rup_sound cl_22281 [cl_1087,cl_20827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1087 v h) (hints_cons _ _ _ (der_20827 v h) (by intro d hd; cases hd)))
def cl_22282 : CNF.NClause := [(4,false),(23,false),(26,true),(11,false),(17,false),(83,true)]
theorem der_22282 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22282 :=
  CNF.rup_sound cl_22282 [cl_1377,cl_17999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1377 v h) (hints_cons _ _ _ (der_17999 v h) (by intro d hd; cases hd)))
def cl_22283 : CNF.NClause := [(83,true),(11,true),(5,true),(26,false),(23,false),(4,false)]
theorem der_22283 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22283 :=
  CNF.rup_sound cl_22283 [cl_1359,cl_15548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1359 v h) (hints_cons _ _ _ (der_15548 v h) (by intro d hd; cases hd)))
def cl_22284 : CNF.NClause := [(17,false),(5,true),(23,true),(11,false),(83,true),(26,false)]
theorem der_22284 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22284 :=
  CNF.rup_sound cl_22284 [cl_1363,cl_21109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1363 v h) (hints_cons _ _ _ (der_21109 v h) (by intro d hd; cases hd)))
def cl_22285 : CNF.NClause := [(4,false),(11,true),(5,true),(23,true),(17,false),(83,true)]
theorem der_22285 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22285 :=
  CNF.rup_sound cl_22285 [cl_1367,cl_21897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1367 v h) (hints_cons _ _ _ (der_21897 v h) (by intro d hd; cases hd)))
def cl_22286 : CNF.NClause := [(83,true),(26,true),(5,true),(23,false),(17,true),(4,false)]
theorem der_22286 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22286 :=
  CNF.rup_sound cl_22286 [cl_1391,cl_18764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1391 v h) (hints_cons _ _ _ (der_18764 v h) (by intro d hd; cases hd)))
def cl_22288 : CNF.NClause := [(63,true),(19,false),(24,true),(4,true),(9,true),(14,false)]
theorem der_22288 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22288 :=
  CNF.rup_sound cl_22288 [cl_116,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_116 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_22289 : CNF.NClause := [(63,false),(25,true),(4,true),(9,true),(19,true),(24,true)]
theorem der_22289 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22289 :=
  CNF.rup_sound cl_22289 [cl_124,cl_17991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_124 v h) (hints_cons _ _ _ (der_17991 v h) (by intro d hd; cases hd)))
def cl_22290 : CNF.NClause := [(63,true),(19,false),(24,false),(14,true),(4,true),(9,true)]
theorem der_22290 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22290 :=
  CNF.rup_sound cl_22290 [cl_104,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_104 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_22291 : CNF.NClause := [(8,true),(30,true),(7,true),(9,true),(6,true),(82,false)]
theorem der_22291 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22291 :=
  CNF.rup_sound cl_22291 [cl_1343,cl_20821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1343 v h) (hints_cons _ _ _ (der_20821 v h) (by intro d hd; cases hd)))
def cl_22292 : CNF.NClause := [(5,false),(9,true),(6,true),(82,true),(7,false),(8,false)]
theorem der_22292 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22292 :=
  CNF.rup_sound cl_22292 [cl_1331,cl_21956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1331 v h) (hints_cons _ _ _ (der_21956 v h) (by intro d hd; cases hd)))
def cl_22293 : CNF.NClause := [(5,false),(7,true),(6,true),(82,true),(9,true),(8,false)]
theorem der_22293 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22293 :=
  CNF.rup_sound cl_22293 [cl_1335,cl_21969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1335 v h) (hints_cons _ _ _ (der_21969 v h) (by intro d hd; cases hd)))
def cl_22294 : CNF.NClause := [(88,true),(9,true),(13,true),(0,true),(17,false),(29,false)]
theorem der_22294 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22294 :=
  CNF.rup_sound cl_22294 [cl_1672,cl_19430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1672 v h) (hints_cons _ _ _ (der_19430 v h) (by intro d hd; cases hd)))
def cl_22295 : CNF.NClause := [(29,false),(9,true),(13,false),(17,true),(88,true),(0,true)]
theorem der_22295 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22295 :=
  CNF.rup_sound cl_22295 [cl_1676,cl_22116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1676 v h) (hints_cons _ _ _ (der_22116 v h) (by intro d hd; cases hd)))
def cl_22296 : CNF.NClause := [(21,false),(29,false),(9,true),(17,true),(88,true),(0,true)]
theorem der_22296 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22296 :=
  CNF.rup_sound cl_22296 [cl_1680,cl_22295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1680 v h) (hints_cons _ _ _ (der_22295 v h) (by intro d hd; cases hd)))
def cl_22298 : CNF.NClause := [(21,false),(13,false),(9,true),(17,false),(88,true),(0,true)]
theorem der_22298 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22298 :=
  CNF.rup_sound cl_22298 [cl_1700,cl_15419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1700 v h) (hints_cons _ _ _ (der_15419 v h) (by intro d hd; cases hd)))
def cl_22299 : CNF.NClause := [(88,true),(17,false),(21,false),(13,true),(0,true),(9,true)]
theorem der_22299 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22299 :=
  CNF.rup_sound cl_22299 [cl_1704,cl_22294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1704 v h) (hints_cons _ _ _ (der_22294 v h) (by intro d hd; cases hd)))
def cl_22300 : CNF.NClause := [(13,false),(88,true),(29,true),(17,true),(21,false),(0,true)]
theorem der_22300 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22300 :=
  CNF.rup_sound cl_22300 [cl_1708,cl_22118] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1708 v h) (hints_cons _ _ _ (der_22118 v h) (by intro d hd; cases hd)))
def cl_22301 : CNF.NClause := [(63,true),(25,false),(9,true),(14,true),(4,false),(24,true)]
theorem der_22301 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22301 :=
  CNF.rup_sound cl_22301 [cl_95,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_95 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_22303 : CNF.NClause := [(63,true),(14,true),(9,true),(19,false),(24,true),(4,false)]
theorem der_22303 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22303 :=
  CNF.rup_sound cl_22303 [cl_119,cl_19927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_119 v h) (hints_cons _ _ _ (der_19927 v h) (by intro d hd; cases hd)))
def cl_22304 : CNF.NClause := [(0,false),(9,true),(13,true),(17,false),(88,true),(29,false)]
theorem der_22304 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22304 :=
  CNF.rup_sound cl_22304 [cl_1671,cl_19430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1671 v h) (hints_cons _ _ _ (der_19430 v h) (by intro d hd; cases hd)))
def cl_22305 : CNF.NClause := [(21,false),(0,false),(9,true),(13,false),(88,true),(29,false)]
theorem der_22305 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22305 :=
  CNF.rup_sound cl_22305 [cl_1675,cl_15419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1675 v h) (hints_cons _ _ _ (der_15419 v h) (by intro d hd; cases hd)))
def cl_22306 : CNF.NClause := [(21,false),(29,false),(9,true),(13,true),(17,true),(88,true)]
theorem der_22306 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22306 :=
  CNF.rup_sound cl_22306 [cl_1679,cl_22296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1679 v h) (hints_cons _ _ _ (der_22296 v h) (by intro d hd; cases hd)))
def cl_22307 : CNF.NClause := [(0,false),(29,false),(9,true),(88,true),(21,true),(17,true)]
theorem der_22307 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22307 :=
  CNF.rup_sound cl_22307 [cl_1695,cl_22120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1695 v h) (hints_cons _ _ _ (der_22120 v h) (by intro d hd; cases hd)))
def cl_22308 : CNF.NClause := [(21,false),(0,false),(9,true),(13,false),(17,false),(88,true)]
theorem der_22308 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22308 :=
  CNF.rup_sound cl_22308 [cl_1699,cl_15419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1699 v h) (hints_cons _ _ _ (der_15419 v h) (by intro d hd; cases hd)))
def cl_22309 : CNF.NClause := [(88,true),(9,true),(21,false),(13,true),(17,false),(29,true)]
theorem der_22309 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22309 :=
  CNF.rup_sound cl_22309 [cl_1703,cl_22299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1703 v h) (hints_cons _ _ _ (der_22299 v h) (by intro d hd; cases hd)))
def cl_22310 : CNF.NClause := [(21,false),(0,false),(9,true),(13,false),(88,true),(29,true)]
theorem der_22310 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22310 :=
  CNF.rup_sound cl_22310 [cl_1707,cl_22308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1707 v h) (hints_cons _ _ _ (der_22308 v h) (by intro d hd; cases hd)))
def cl_22311 : CNF.NClause := [(21,false),(9,true),(88,true),(0,false),(17,true),(29,true)]
theorem der_22311 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22311 :=
  CNF.rup_sound cl_22311 [cl_1711,cl_22310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1711 v h) (hints_cons _ _ _ (der_22310 v h) (by intro d hd; cases hd)))
def cl_22312 : CNF.NClause := [(6,false),(7,false),(82,true),(30,true),(9,true),(5,true)]
theorem der_22312 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22312 :=
  CNF.rup_sound cl_22312 [cl_1338,cl_21843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1338 v h) (hints_cons _ _ _ (der_21843 v h) (by intro d hd; cases hd)))
def cl_22313 : CNF.NClause := [(75,true),(3,false),(10,false),(16,false),(9,true),(26,false)]
theorem der_22313 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22313 :=
  CNF.rup_sound cl_22313 [cl_851,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_851 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_22314 : CNF.NClause := [(22,true),(75,true),(26,false),(3,false),(9,true),(10,false)]
theorem der_22314 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22314 :=
  CNF.rup_sound cl_22314 [cl_859,cl_22313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_859 v h) (hints_cons _ _ _ (der_22313 v h) (by intro d hd; cases hd)))
def cl_22315 : CNF.NClause := [(75,true),(3,false),(10,false),(16,false),(9,true),(22,true)]
theorem der_22315 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22315 :=
  CNF.rup_sound cl_22315 [cl_883,cl_22313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_883 v h) (hints_cons _ _ _ (der_22313 v h) (by intro d hd; cases hd)))
def cl_22316 : CNF.NClause := [(10,false),(3,false),(26,true),(9,true),(75,true),(16,true)]
theorem der_22316 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22316 :=
  CNF.rup_sound cl_22316 [cl_891,cl_17644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_891 v h) (hints_cons _ _ _ (der_17644 v h) (by intro d hd; cases hd)))
def cl_22317 : CNF.NClause := [(75,true),(26,false),(16,false),(3,false),(10,true),(9,true)]
theorem der_22317 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22317 :=
  CNF.rup_sound cl_22317 [cl_855,cl_15425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_855 v h) (hints_cons _ _ _ (der_15425 v h) (by intro d hd; cases hd)))
def cl_22319 : CNF.NClause := [(75,true),(10,true),(16,true),(9,true),(22,false),(3,false)]
theorem der_22319 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22319 :=
  CNF.rup_sound cl_22319 [cl_879,cl_22006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_879 v h) (hints_cons _ _ _ (der_22006 v h) (by intro d hd; cases hd)))
def cl_22320 : CNF.NClause := [(75,true),(26,true),(3,false),(9,true),(22,true),(16,false)]
theorem der_22320 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22320 :=
  CNF.rup_sound cl_22320 [cl_887,cl_22315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_887 v h) (hints_cons _ _ _ (der_22315 v h) (by intro d hd; cases hd)))
def cl_22322 : CNF.NClause := [(30,false),(5,false),(82,true),(9,true),(8,true),(7,true)]
theorem der_22322 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22322 :=
  CNF.rup_sound cl_22322 [cl_1311,cl_15595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1311 v h) (hints_cons _ _ _ (der_15595 v h) (by intro d hd; cases hd)))
def cl_22323 : CNF.NClause := [(68,true),(8,true),(29,false),(12,false),(16,false),(4,true)]
theorem der_22323 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22323 :=
  CNF.rup_sound cl_22323 [cl_404,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_404 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22325 : CNF.NClause := [(68,true),(8,true),(16,false),(20,false),(4,true),(12,false)]
theorem der_22325 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22325 :=
  CNF.rup_sound cl_22325 [cl_420,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_420 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22326 : CNF.NClause := [(79,true),(26,false),(14,true),(21,true),(15,false),(2,true)]
theorem der_22326 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22326 :=
  CNF.rup_sound cl_22326 [cl_1112,cl_20530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1112 v h) (hints_cons _ _ _ (der_20530 v h) (by intro d hd; cases hd)))
def cl_22327 : CNF.NClause := [(79,true),(26,true),(21,false),(8,true),(2,true),(15,false)]
theorem der_22327 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22327 :=
  CNF.rup_sound cl_22327 [cl_1128,cl_22105] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1128 v h) (hints_cons _ _ _ (der_22105 v h) (by intro d hd; cases hd)))
def cl_22328 : CNF.NClause := [(79,false),(26,true),(8,true),(2,true),(14,true),(21,true)]
theorem der_22328 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22328 :=
  CNF.rup_sound cl_22328 [cl_1144,cl_18884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1144 v h) (hints_cons _ _ _ (der_18884 v h) (by intro d hd; cases hd)))
def cl_22329 : CNF.NClause := [(13,false),(65,true),(3,true),(8,true),(18,true),(25,false)]
theorem der_22329 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22329 :=
  CNF.rup_sound cl_22329 [cl_220,cl_20243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_220 v h) (hints_cons _ _ _ (der_20243 v h) (by intro d hd; cases hd)))
def cl_22330 : CNF.NClause := [(90,true),(19,false),(0,true),(11,false),(28,false),(8,true)]
theorem der_22330 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22330 :=
  CNF.rup_sound cl_22330 [cl_1812,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1812 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_22331 : CNF.NClause := [(90,true),(22,true),(19,false),(11,false),(8,true),(0,true)]
theorem der_22331 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22331 :=
  CNF.rup_sound cl_22331 [cl_1844,cl_22330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1844 v h) (hints_cons _ _ _ (der_22330 v h) (by intro d hd; cases hd)))
def cl_22332 : CNF.NClause := [(27,false),(24,false),(1,true),(10,false),(8,true),(76,true)]
theorem der_22332 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22332 :=
  CNF.rup_sound cl_22332 [cl_908,cl_15415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_908 v h) (hints_cons _ _ _ (der_15415 v h) (by intro d hd; cases hd)))
def cl_22333 : CNF.NClause := [(76,true),(10,false),(1,true),(27,false),(17,false),(8,true)]
theorem der_22333 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22333 :=
  CNF.rup_sound cl_22333 [cl_916,cl_15415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_916 v h) (hints_cons _ _ _ (der_15415 v h) (by intro d hd; cases hd)))
def cl_22334 : CNF.NClause := [(10,false),(27,false),(1,true),(8,true),(76,true),(17,true)]
theorem der_22334 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22334 :=
  CNF.rup_sound cl_22334 [cl_924,cl_22332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_924 v h) (hints_cons _ _ _ (der_22332 v h) (by intro d hd; cases hd)))
def cl_22335 : CNF.NClause := [(10,false),(76,true),(1,true),(8,true),(24,false),(27,true)]
theorem der_22335 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22335 :=
  CNF.rup_sound cl_22335 [cl_940,cl_17637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_940 v h) (hints_cons _ _ _ (der_17637 v h) (by intro d hd; cases hd)))
def cl_22336 : CNF.NClause := [(27,true),(1,true),(76,false),(24,true),(8,true),(17,true)]
theorem der_22336 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22336 :=
  CNF.rup_sound cl_22336 [cl_956,cl_17896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_956 v h) (hints_cons _ _ _ (der_17896 v h) (by intro d hd; cases hd)))
def cl_22337 : CNF.NClause := [(13,false),(65,true),(8,true),(18,true),(23,true),(25,false)]
theorem der_22337 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22337 :=
  CNF.rup_sound cl_22337 [cl_219,cl_19979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_219 v h) (hints_cons _ _ _ (der_19979 v h) (by intro d hd; cases hd)))
def cl_22338 : CNF.NClause := [(65,true),(23,true),(25,false),(3,false),(18,true),(8,true)]
theorem der_22338 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22338 :=
  CNF.rup_sound cl_22338 [cl_223,cl_22337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_223 v h) (hints_cons _ _ _ (der_22337 v h) (by intro d hd; cases hd)))
def cl_22339 : CNF.NClause := [(18,false),(8,true),(3,false),(65,true),(23,false),(25,true)]
theorem der_22339 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22339 :=
  CNF.rup_sound cl_22339 [cl_227,cl_21907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_227 v h) (hints_cons _ _ _ (der_21907 v h) (by intro d hd; cases hd)))
def cl_22340 : CNF.NClause := [(65,true),(8,true),(3,false),(18,true),(23,false),(25,true)]
theorem der_22340 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22340 :=
  CNF.rup_sound cl_22340 [cl_235,cl_21907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_235 v h) (hints_cons _ _ _ (der_21907 v h) (by intro d hd; cases hd)))
def cl_22341 : CNF.NClause := [(13,false),(18,false),(8,true),(3,false),(65,true),(25,true)]
theorem der_22341 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22341 :=
  CNF.rup_sound cl_22341 [cl_243,cl_22339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_243 v h) (hints_cons _ _ _ (der_22339 v h) (by intro d hd; cases hd)))
def cl_22342 : CNF.NClause := [(18,false),(8,true),(25,true),(3,false),(13,true),(65,true)]
theorem der_22342 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22342 :=
  CNF.rup_sound cl_22342 [cl_247,cl_21949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_247 v h) (hints_cons _ _ _ (der_21949 v h) (by intro d hd; cases hd)))
def cl_22343 : CNF.NClause := [(13,false),(65,true),(8,true),(3,false),(18,true),(23,true)]
theorem der_22343 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22343 :=
  CNF.rup_sound cl_22343 [cl_251,cl_22337] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_251 v h) (hints_cons _ _ _ (der_22337 v h) (by intro d hd; cases hd)))
def cl_22344 : CNF.NClause := [(79,true),(2,true),(21,false),(15,false),(8,true),(26,false)]
theorem der_22344 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22344 :=
  CNF.rup_sound cl_22344 [cl_1096,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1096 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_22345 : CNF.NClause := [(79,true),(26,false),(21,false),(8,true),(15,false),(2,false)]
theorem der_22345 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22345 :=
  CNF.rup_sound cl_22345 [cl_1095,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1095 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_22346 : CNF.NClause := [(79,true),(21,false),(2,false),(8,true),(14,false),(26,false)]
theorem der_22346 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22346 :=
  CNF.rup_sound cl_22346 [cl_1099,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1099 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_22347 : CNF.NClause := [(79,true),(15,true),(21,false),(14,true),(2,false),(26,false)]
theorem der_22347 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22347 :=
  CNF.rup_sound cl_22347 [cl_1103,cl_21965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1103 v h) (hints_cons _ _ _ (der_21965 v h) (by intro d hd; cases hd)))
def cl_22348 : CNF.NClause := [(79,true),(15,false),(26,false),(8,true),(21,true),(2,false)]
theorem der_22348 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22348 :=
  CNF.rup_sound cl_22348 [cl_1111,cl_20782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1111 v h) (hints_cons _ _ _ (der_20782 v h) (by intro d hd; cases hd)))
def cl_22349 : CNF.NClause := [(79,true),(21,true),(2,false),(8,true),(14,false),(26,false)]
theorem der_22349 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22349 :=
  CNF.rup_sound cl_22349 [cl_1115,cl_20782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1115 v h) (hints_cons _ _ _ (der_20782 v h) (by intro d hd; cases hd)))
def cl_22350 : CNF.NClause := [(79,true),(15,true),(26,false),(8,true),(14,true),(2,false)]
theorem der_22350 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22350 :=
  CNF.rup_sound cl_22350 [cl_1119,cl_22347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1119 v h) (hints_cons _ _ _ (der_22347 v h) (by intro d hd; cases hd)))
def cl_22351 : CNF.NClause := [(79,true),(21,false),(2,false),(15,false),(14,false),(8,true)]
theorem der_22351 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22351 :=
  CNF.rup_sound cl_22351 [cl_1123,cl_15290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1123 v h) (hints_cons _ _ _ (der_15290 v h) (by intro d hd; cases hd)))
def cl_22352 : CNF.NClause := [(79,true),(8,true),(2,false),(14,true),(15,false),(26,true)]
theorem der_22352 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22352 :=
  CNF.rup_sound cl_22352 [cl_1127,cl_17836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1127 v h) (hints_cons _ _ _ (der_17836 v h) (by intro d hd; cases hd)))
def cl_22353 : CNF.NClause := [(79,true),(15,true),(21,false),(2,false),(8,true),(14,false)]
theorem der_22353 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22353 :=
  CNF.rup_sound cl_22353 [cl_1131,cl_22346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1131 v h) (hints_cons _ _ _ (der_22346 v h) (by intro d hd; cases hd)))
def cl_22354 : CNF.NClause := [(79,true),(15,true),(8,true),(14,true),(2,false),(21,false)]
theorem der_22354 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22354 :=
  CNF.rup_sound cl_22354 [cl_1135,cl_22347] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1135 v h) (hints_cons _ _ _ (der_22347 v h) (by intro d hd; cases hd)))
def cl_22355 : CNF.NClause := [(79,true),(2,false),(21,true),(8,true),(26,true),(14,false)]
theorem der_22355 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22355 :=
  CNF.rup_sound cl_22355 [cl_1147,cl_20782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1147 v h) (hints_cons _ _ _ (der_20782 v h) (by intro d hd; cases hd)))
def cl_22356 : CNF.NClause := [(27,false),(10,false),(8,true),(24,false),(76,true),(17,true)]
theorem der_22356 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22356 :=
  CNF.rup_sound cl_22356 [cl_907,cl_22334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_907 v h) (hints_cons _ _ _ (der_22334 v h) (by intro d hd; cases hd)))
def cl_22357 : CNF.NClause := [(17,false),(27,false),(1,false),(8,true),(10,false),(76,true)]
theorem der_22357 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22357 :=
  CNF.rup_sound cl_22357 [cl_915,cl_15415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_915 v h) (hints_cons _ _ _ (der_15415 v h) (by intro d hd; cases hd)))
def cl_22358 : CNF.NClause := [(10,false),(76,true),(8,true),(24,true),(27,false),(17,true)]
theorem der_22358 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22358 :=
  CNF.rup_sound cl_22358 [cl_923,cl_22334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_923 v h) (hints_cons _ _ _ (der_22334 v h) (by intro d hd; cases hd)))
def cl_22359 : CNF.NClause := [(17,false),(1,false),(8,true),(24,false),(76,true),(27,true)]
theorem der_22359 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22359 :=
  CNF.rup_sound cl_22359 [cl_931,cl_22042] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_931 v h) (hints_cons _ _ _ (der_22042 v h) (by intro d hd; cases hd)))
def cl_22360 : CNF.NClause := [(76,true),(10,false),(8,true),(17,true),(24,false),(27,true)]
theorem der_22360 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22360 :=
  CNF.rup_sound cl_22360 [cl_939,cl_22335] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_939 v h) (hints_cons _ _ _ (der_22335 v h) (by intro d hd; cases hd)))
def cl_22361 : CNF.NClause := [(17,false),(10,false),(1,false),(8,true),(24,true),(76,true)]
theorem der_22361 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22361 :=
  CNF.rup_sound cl_22361 [cl_947,cl_22357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_947 v h) (hints_cons _ _ _ (der_22357 v h) (by intro d hd; cases hd)))
def cl_22362 : CNF.NClause := [(76,true),(10,false),(1,false),(8,true),(17,true),(27,true)]
theorem der_22362 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22362 :=
  CNF.rup_sound cl_22362 [cl_955,cl_22360] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_955 v h) (hints_cons _ _ _ (der_22360 v h) (by intro d hd; cases hd)))
def cl_22363 : CNF.NClause := [(68,true),(4,false),(20,true),(8,true),(29,false),(12,false)]
theorem der_22363 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22363 :=
  CNF.rup_sound cl_22363 [cl_403,cl_17664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_403 v h) (hints_cons _ _ _ (der_17664 v h) (by intro d hd; cases hd)))
def cl_22364 : CNF.NClause := [(12,true),(68,true),(16,false),(29,false),(4,false),(8,true)]
theorem der_22364 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22364 :=
  CNF.rup_sound cl_22364 [cl_407,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_407 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22365 : CNF.NClause := [(68,true),(4,false),(29,true),(8,true),(12,false),(20,false)]
theorem der_22365 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22365 :=
  CNF.rup_sound cl_22365 [cl_419,cl_17664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_419 v h) (hints_cons _ _ _ (der_17664 v h) (by intro d hd; cases hd)))
def cl_22366 : CNF.NClause := [(68,true),(12,true),(16,false),(20,false),(4,false),(8,true)]
theorem der_22366 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22366 :=
  CNF.rup_sound cl_22366 [cl_423,cl_21860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_423 v h) (hints_cons _ _ _ (der_21860 v h) (by intro d hd; cases hd)))
def cl_22368 : CNF.NClause := [(68,true),(12,true),(8,true),(16,false),(4,false),(20,true)]
theorem der_22368 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22368 :=
  CNF.rup_sound cl_22368 [cl_439,cl_22364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_439 v h) (hints_cons _ _ _ (der_22364 v h) (by intro d hd; cases hd)))
def cl_22369 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(22,false),(28,false)]
theorem der_22369 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22369 :=
  CNF.rup_sound cl_22369 [cl_1807,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1807 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_22370 : CNF.NClause := [(90,true),(0,false),(8,true),(11,false),(19,false),(28,false)]
theorem der_22370 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22370 :=
  CNF.rup_sound cl_22370 [cl_1811,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1811 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_22371 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(19,false),(28,false)]
theorem der_22371 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22371 :=
  CNF.rup_sound cl_22371 [cl_1815,cl_21857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1815 v h) (hints_cons _ _ _ (der_21857 v h) (by intro d hd; cases hd)))
def cl_22372 : CNF.NClause := [(90,true),(8,true),(11,false),(19,true),(22,true),(28,false)]
theorem der_22372 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22372 :=
  CNF.rup_sound cl_22372 [cl_1819,cl_20799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1819 v h) (hints_cons _ _ _ (der_20799 v h) (by intro d hd; cases hd)))
def cl_22373 : CNF.NClause := [(90,true),(0,false),(8,true),(11,true),(22,true),(28,false)]
theorem der_22373 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22373 :=
  CNF.rup_sound cl_22373 [cl_1823,cl_22371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1823 v h) (hints_cons _ _ _ (der_22371 v h) (by intro d hd; cases hd)))
def cl_22374 : CNF.NClause := [(90,true),(11,true),(0,false),(19,true),(22,false),(28,true)]
theorem der_22374 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22374 :=
  CNF.rup_sound cl_22374 [cl_1839,cl_20427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1839 v h) (hints_cons _ _ _ (der_20427 v h) (by intro d hd; cases hd)))
def cl_22375 : CNF.NClause := [(90,true),(22,true),(8,true),(11,false),(19,false),(28,true)]
theorem der_22375 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22375 :=
  CNF.rup_sound cl_22375 [cl_1843,cl_22331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1843 v h) (hints_cons _ _ _ (der_22331 v h) (by intro d hd; cases hd)))
def cl_22376 : CNF.NClause := [(90,true),(11,true),(8,true),(0,false),(19,false),(28,true)]
theorem der_22376 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22376 :=
  CNF.rup_sound cl_22376 [cl_1847,cl_21986] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1847 v h) (hints_cons _ _ _ (der_21986 v h) (by intro d hd; cases hd)))
def cl_22377 : CNF.NClause := [(90,true),(22,true),(11,false),(19,true),(0,false),(28,true)]
theorem der_22377 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22377 :=
  CNF.rup_sound cl_22377 [cl_1851,cl_21942] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1851 v h) (hints_cons _ _ _ (der_21942 v h) (by intro d hd; cases hd)))
def cl_22378 : CNF.NClause := [(82,false),(7,true),(8,true),(9,true),(5,true),(6,true)]
theorem der_22378 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22378 :=
  CNF.rup_sound cl_22378 [cl_1312,cl_20821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1312 v h) (hints_cons _ _ _ (der_20821 v h) (by intro d hd; cases hd)))
def cl_22379 : CNF.NClause := [(69,false),(11,true),(9,true),(2,true),(18,true),(20,true)]
theorem der_22379 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22379 :=
  CNF.rup_sound cl_22379 [cl_480,cl_19607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_480 v h) (hints_cons _ _ _ (der_19607 v h) (by intro d hd; cases hd)))
def cl_22380 : CNF.NClause := [(11,true),(2,true),(27,true),(69,false),(20,true),(9,true)]
theorem der_22380 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22380 :=
  CNF.rup_sound cl_22380 [cl_504,cl_19607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_504 v h) (hints_cons _ _ _ (der_19607 v h) (by intro d hd; cases hd)))
def cl_22381 : CNF.NClause := [(69,false),(2,true),(9,true),(20,true),(18,true),(27,true)]
theorem der_22381 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22381 :=
  CNF.rup_sound cl_22381 [cl_508,cl_19607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_508 v h) (hints_cons _ _ _ (der_19607 v h) (by intro d hd; cases hd)))
def cl_22382 : CNF.NClause := [(69,false),(11,true),(20,true),(18,true),(27,true),(2,true)]
theorem der_22382 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22382 :=
  CNF.rup_sound cl_22382 [cl_510,cl_19607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_510 v h) (hints_cons _ _ _ (der_19607 v h) (by intro d hd; cases hd)))
def cl_22383 : CNF.NClause := [(69,false),(11,true),(20,true),(9,true),(27,true),(18,true)]
theorem der_22383 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22383 :=
  CNF.rup_sound cl_22383 [cl_511,cl_19607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_511 v h) (hints_cons _ _ _ (der_19607 v h) (by intro d hd; cases hd)))
def cl_22384 : CNF.NClause := [(58,false),(69,false),(27,true),(85,false),(89,false),(78,false)]
theorem der_22384 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22384 :=
  CNF.rup_sound cl_22384 [cl_20382,cl_20395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20382 v h) (hints_cons _ _ _ (der_20395 v h) (by intro d hd; cases hd)))
def cl_22385 : CNF.NClause := [(11,true),(10,true),(14,true),(12,true),(72,false),(13,true)]
theorem der_22385 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22385 :=
  CNF.rup_sound cl_22385 [cl_672,cl_20025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_672 v h) (hints_cons _ _ _ (der_20025 v h) (by intro d hd; cases hd)))
def cl_22386 : CNF.NClause := [(72,false),(11,true),(10,true),(13,true),(14,true),(30,true)]
theorem der_22386 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22386 :=
  CNF.rup_sound cl_22386 [cl_700,cl_22096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_700 v h) (hints_cons _ _ _ (der_22096 v h) (by intro d hd; cases hd)))
def cl_22387 : CNF.NClause := [(72,false),(14,true),(13,true),(10,true),(12,true),(30,true)]
theorem der_22387 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22387 :=
  CNF.rup_sound cl_22387 [cl_702,cl_22096] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_702 v h) (hints_cons _ _ _ (der_22096 v h) (by intro d hd; cases hd)))
def cl_22388 : CNF.NClause := [(11,true),(13,true),(12,true),(72,false),(14,true),(30,true)]
theorem der_22388 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22388 :=
  CNF.rup_sound cl_22388 [cl_703,cl_20025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_703 v h) (hints_cons _ _ _ (der_20025 v h) (by intro d hd; cases hd)))
def cl_22389 : CNF.NClause := [(15,true),(16,true),(17,true),(19,true),(18,true),(77,false)]
theorem der_22389 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22389 :=
  CNF.rup_sound cl_22389 [cl_992,cl_19383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_992 v h) (hints_cons _ _ _ (der_19383 v h) (by intro d hd; cases hd)))
def cl_22390 : CNF.NClause := [(15,true),(77,false),(16,true),(17,true),(18,true),(30,true)]
theorem der_22390 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22390 :=
  CNF.rup_sound cl_22390 [cl_1008,cl_19383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1008 v h) (hints_cons _ _ _ (der_19383 v h) (by intro d hd; cases hd)))
def cl_22391 : CNF.NClause := [(16,true),(15,true),(19,true),(17,true),(77,false),(30,true)]
theorem der_22391 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22391 :=
  CNF.rup_sound cl_22391 [cl_1016,cl_19383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1016 v h) (hints_cons _ _ _ (der_19383 v h) (by intro d hd; cases hd)))
def cl_22392 : CNF.NClause := [(77,false),(16,true),(19,true),(18,true),(15,true),(30,true)]
theorem der_22392 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22392 :=
  CNF.rup_sound cl_22392 [cl_1020,cl_19383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1020 v h) (hints_cons _ _ _ (der_19383 v h) (by intro d hd; cases hd)))
def cl_22393 : CNF.NClause := [(77,false),(19,true),(15,true),(17,true),(18,true),(30,true)]
theorem der_22393 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22393 :=
  CNF.rup_sound cl_22393 [cl_1022,cl_19383] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1022 v h) (hints_cons _ _ _ (der_19383 v h) (by intro d hd; cases hd)))
def cl_22395 : CNF.NClause := [(11,true),(23,true),(17,true),(5,true),(4,true),(83,false)]
theorem der_22395 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22395 :=
  CNF.rup_sound cl_22395 [cl_1376,cl_19541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1376 v h) (hints_cons _ _ _ (der_19541 v h) (by intro d hd; cases hd)))
def cl_22396 : CNF.NClause := [(23,true),(11,true),(5,true),(26,true),(83,false),(4,true)]
theorem der_22396 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22396 :=
  CNF.rup_sound cl_22396 [cl_1400,cl_19541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1400 v h) (hints_cons _ _ _ (der_19541 v h) (by intro d hd; cases hd)))
def cl_22397 : CNF.NClause := [(83,false),(23,true),(26,true),(5,true),(4,true),(17,true)]
theorem der_22397 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22397 :=
  CNF.rup_sound cl_22397 [cl_1404,cl_19541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1404 v h) (hints_cons _ _ _ (der_19541 v h) (by intro d hd; cases hd)))
def cl_22398 : CNF.NClause := [(83,false),(26,true),(11,true),(4,true),(17,true),(23,true)]
theorem der_22398 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22398 :=
  CNF.rup_sound cl_22398 [cl_1406,cl_19541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1406 v h) (hints_cons _ _ _ (der_19541 v h) (by intro d hd; cases hd)))
def cl_22399 : CNF.NClause := [(71,false),(13,true),(1,true),(19,true),(20,true),(7,true)]
theorem der_22399 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22399 :=
  CNF.rup_sound cl_22399 [cl_608,cl_19243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_608 v h) (hints_cons _ _ _ (der_19243 v h) (by intro d hd; cases hd)))
def cl_22400 : CNF.NClause := [(71,false),(26,true),(13,true),(1,true),(19,true),(7,true)]
theorem der_22400 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22400 :=
  CNF.rup_sound cl_22400 [cl_624,cl_19243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_624 v h) (hints_cons _ _ _ (der_19243 v h) (by intro d hd; cases hd)))
def cl_22401 : CNF.NClause := [(71,false),(20,true),(7,true),(13,true),(1,true),(26,true)]
theorem der_22401 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22401 :=
  CNF.rup_sound cl_22401 [cl_632,cl_19243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_632 v h) (hints_cons _ _ _ (der_19243 v h) (by intro d hd; cases hd)))
def cl_22402 : CNF.NClause := [(71,false),(26,true),(19,true),(13,true),(1,true),(20,true)]
theorem der_22402 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22402 :=
  CNF.rup_sound cl_22402 [cl_638,cl_19243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_638 v h) (hints_cons _ _ _ (der_19243 v h) (by intro d hd; cases hd)))
def cl_22403 : CNF.NClause := [(57,false),(75,true),(26,true),(71,false),(79,false),(91,false)]
theorem der_22403 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22403 :=
  CNF.rup_sound cl_22403 [cl_20200,cl_18388] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20200 v h) (hints_cons _ _ _ (der_18388 v h) (by intro d hd; cases hd)))
def cl_22404 : CNF.NClause := [(15,true),(78,false),(6,true),(4,true),(13,true),(22,true)]
theorem der_22404 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22404 :=
  CNF.rup_sound cl_22404 [cl_1056,cl_20827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1056 v h) (hints_cons _ _ _ (der_20827 v h) (by intro d hd; cases hd)))
def cl_22405 : CNF.NClause := [(78,false),(22,true),(6,true),(13,true),(4,true),(27,true)]
theorem der_22405 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22405 :=
  CNF.rup_sound cl_22405 [cl_1080,cl_20827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1080 v h) (hints_cons _ _ _ (der_20827 v h) (by intro d hd; cases hd)))
def cl_22406 : CNF.NClause := [(4,true),(15,true),(6,true),(78,false),(22,true),(27,true)]
theorem der_22406 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22406 :=
  CNF.rup_sound cl_22406 [cl_1084,cl_20827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1084 v h) (hints_cons _ _ _ (der_20827 v h) (by intro d hd; cases hd)))
def cl_22407 : CNF.NClause := [(4,true),(22,true),(78,false),(13,true),(15,true),(27,true)]
theorem der_22407 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22407 :=
  CNF.rup_sound cl_22407 [cl_1086,cl_20827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1086 v h) (hints_cons _ _ _ (der_20827 v h) (by intro d hd; cases hd)))
def cl_22408 : CNF.NClause := [(76,false),(24,true),(1,true),(8,true),(10,true),(17,true)]
theorem der_22408 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22408 :=
  CNF.rup_sound cl_22408 [cl_928,cl_17896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_928 v h) (hints_cons _ _ _ (der_17896 v h) (by intro d hd; cases hd)))
def cl_22409 : CNF.NClause := [(76,false),(24,true),(1,true),(27,true),(10,true),(8,true)]
theorem der_22409 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22409 :=
  CNF.rup_sound cl_22409 [cl_952,cl_17896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_952 v h) (hints_cons _ _ _ (der_17896 v h) (by intro d hd; cases hd)))
def cl_22410 : CNF.NClause := [(76,false),(17,true),(24,true),(1,true),(10,true),(27,true)]
theorem der_22410 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22410 :=
  CNF.rup_sound cl_22410 [cl_958,cl_17896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_958 v h) (hints_cons _ _ _ (der_17896 v h) (by intro d hd; cases hd)))
def cl_22412 : CNF.NClause := [(73,false),(21,true),(4,true),(10,true),(18,true),(7,true)]
theorem der_22412 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22412 :=
  CNF.rup_sound cl_22412 [cl_736,cl_20016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_736 v h) (hints_cons _ _ _ (der_20016 v h) (by intro d hd; cases hd)))
def cl_22413 : CNF.NClause := [(73,false),(28,true),(4,true),(10,true),(7,true),(18,true)]
theorem der_22413 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22413 :=
  CNF.rup_sound cl_22413 [cl_752,cl_20016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_752 v h) (hints_cons _ _ _ (der_20016 v h) (by intro d hd; cases hd)))
def cl_22414 : CNF.NClause := [(4,true),(28,true),(7,true),(21,true),(73,false),(10,true)]
theorem der_22414 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22414 :=
  CNF.rup_sound cl_22414 [cl_760,cl_20016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_760 v h) (hints_cons _ _ _ (der_20016 v h) (by intro d hd; cases hd)))
def cl_22415 : CNF.NClause := [(73,false),(28,true),(21,true),(10,true),(18,true),(4,true)]
theorem der_22415 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22415 :=
  CNF.rup_sound cl_22415 [cl_766,cl_20016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_766 v h) (hints_cons _ _ _ (der_20016 v h) (by intro d hd; cases hd)))
def cl_22417 : CNF.NClause := [(84,true),(2,true),(24,false),(13,false),(16,false),(5,true)]
theorem der_22417 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22417 :=
  CNF.rup_sound cl_22417 [cl_1444,cl_15185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1444 v h) (hints_cons _ _ _ (der_15185 v h) (by intro d hd; cases hd)))
def cl_22418 : CNF.NClause := [(84,true),(16,true),(13,false),(24,false),(5,true),(2,true)]
theorem der_22418 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22418 :=
  CNF.rup_sound cl_22418 [cl_1452,cl_21911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1452 v h) (hints_cons _ _ _ (der_21911 v h) (by intro d hd; cases hd)))
def cl_22419 : CNF.NClause := [(84,true),(2,true),(24,true),(13,false),(5,true),(16,false)]
theorem der_22419 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22419 :=
  CNF.rup_sound cl_22419 [cl_1460,cl_21913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1460 v h) (hints_cons _ _ _ (der_21913 v h) (by intro d hd; cases hd)))
def cl_22420 : CNF.NClause := [(84,false),(2,true),(24,true),(5,true),(28,true),(16,true)]
theorem der_22420 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22420 :=
  CNF.rup_sound cl_22420 [cl_1468,cl_19228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1468 v h) (hints_cons _ _ _ (der_19228 v h) (by intro d hd; cases hd)))
def cl_22421 : CNF.NClause := [(85,true),(27,false),(3,true),(12,false),(5,true),(21,false)]
theorem der_22421 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22421 :=
  CNF.rup_sound cl_22421 [cl_1484,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1484 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22422 : CNF.NClause := [(85,true),(3,true),(12,false),(27,false),(19,false),(5,true)]
theorem der_22422 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22422 :=
  CNF.rup_sound cl_22422 [cl_1492,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1492 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22423 : CNF.NClause := [(85,true),(19,true),(27,false),(5,true),(12,false),(21,true)]
theorem der_22423 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22423 :=
  CNF.rup_sound cl_22423 [cl_1500,cl_20807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1500 v h) (hints_cons _ _ _ (der_20807 v h) (by intro d hd; cases hd)))
def cl_22424 : CNF.NClause := [(85,true),(19,false),(3,true),(12,false),(21,false),(5,true)]
theorem der_22424 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22424 :=
  CNF.rup_sound cl_22424 [cl_1508,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1508 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22425 : CNF.NClause := [(85,true),(12,false),(21,false),(3,true),(5,true),(19,true)]
theorem der_22425 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22425 :=
  CNF.rup_sound cl_22425 [cl_1516,cl_22421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1516 v h) (hints_cons _ _ _ (der_22421 v h) (by intro d hd; cases hd)))
def cl_22426 : CNF.NClause := [(85,true),(3,true),(12,false),(19,false),(21,true),(5,true)]
theorem der_22426 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22426 :=
  CNF.rup_sound cl_22426 [cl_1524,cl_22422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1524 v h) (hints_cons _ _ _ (der_22422 v h) (by intro d hd; cases hd)))
def cl_22427 : CNF.NClause := [(10,false),(0,true),(92,true),(5,true),(20,false),(25,false)]
theorem der_22427 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22427 :=
  CNF.rup_sound cl_22427 [cl_1932,cl_21912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1932 v h) (hints_cons _ _ _ (der_21912 v h) (by intro d hd; cases hd)))
def cl_22428 : CNF.NClause := [(10,false),(25,false),(20,true),(0,true),(5,true),(92,true)]
theorem der_22428 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22428 :=
  CNF.rup_sound cl_22428 [cl_1948,cl_21912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1948 v h) (hints_cons _ _ _ (der_21912 v h) (by intro d hd; cases hd)))
def cl_22429 : CNF.NClause := [(10,false),(25,true),(20,false),(0,true),(5,true),(92,true)]
theorem der_22429 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22429 :=
  CNF.rup_sound cl_22429 [cl_1964,cl_21912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1964 v h) (hints_cons _ _ _ (der_21912 v h) (by intro d hd; cases hd)))
def cl_22430 : CNF.NClause := [(25,true),(0,true),(20,true),(92,false),(5,true),(15,true)]
theorem der_22430 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22430 :=
  CNF.rup_sound cl_22430 [cl_1980,cl_18125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1980 v h) (hints_cons _ _ _ (der_18125 v h) (by intro d hd; cases hd)))
def cl_22431 : CNF.NClause := [(82,false),(30,true),(7,true),(5,true),(9,true),(8,true)]
theorem der_22431 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22431 :=
  CNF.rup_sound cl_22431 [cl_1342,cl_20821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1342 v h) (hints_cons _ _ _ (der_20821 v h) (by intro d hd; cases hd)))
def cl_22432 : CNF.NClause := [(86,true),(14,true),(29,false),(1,true),(5,true),(22,false)]
theorem der_22432 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22432 :=
  CNF.rup_sound cl_22432 [cl_1552,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1552 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22433 : CNF.NClause := [(86,true),(1,true),(5,true),(14,true),(18,false),(29,false)]
theorem der_22433 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22433 :=
  CNF.rup_sound cl_22433 [cl_1560,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1560 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22434 : CNF.NClause := [(28,false),(84,true),(5,true),(2,false),(16,true),(24,true)]
theorem der_22434 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22434 :=
  CNF.rup_sound cl_22434 [cl_1435,cl_18751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1435 v h) (hints_cons _ _ _ (der_18751 v h) (by intro d hd; cases hd)))
def cl_22435 : CNF.NClause := [(84,true),(13,false),(5,true),(24,false),(2,false),(16,false)]
theorem der_22435 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22435 :=
  CNF.rup_sound cl_22435 [cl_1443,cl_15185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1443 v h) (hints_cons _ _ _ (der_15185 v h) (by intro d hd; cases hd)))
def cl_22436 : CNF.NClause := [(84,true),(5,true),(2,false),(24,false),(13,true),(28,true)]
theorem der_22436 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22436 :=
  CNF.rup_sound cl_22436 [cl_1455,cl_21950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1455 v h) (hints_cons _ _ _ (der_21950 v h) (by intro d hd; cases hd)))
def cl_22437 : CNF.NClause := [(84,true),(13,false),(5,true),(24,true),(2,false),(16,false)]
theorem der_22437 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22437 :=
  CNF.rup_sound cl_22437 [cl_1459,cl_21913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1459 v h) (hints_cons _ _ _ (der_21913 v h) (by intro d hd; cases hd)))
def cl_22438 : CNF.NClause := [(86,true),(1,false),(5,true),(18,false),(14,false),(29,false)]
theorem der_22438 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22438 :=
  CNF.rup_sound cl_22438 [cl_1555,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1555 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22439 : CNF.NClause := [(86,true),(1,false),(5,true),(18,false),(14,true),(29,false)]
theorem der_22439 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22439 :=
  CNF.rup_sound cl_22439 [cl_1559,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1559 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22440 : CNF.NClause := [(86,true),(1,false),(5,true),(18,true),(14,false),(29,false)]
theorem der_22440 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22440 :=
  CNF.rup_sound cl_22440 [cl_1563,cl_21850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1563 v h) (hints_cons _ _ _ (der_21850 v h) (by intro d hd; cases hd)))
def cl_22441 : CNF.NClause := [(86,true),(1,false),(5,true),(18,true),(14,true),(29,false)]
theorem der_22441 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22441 :=
  CNF.rup_sound cl_22441 [cl_1567,cl_21850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1567 v h) (hints_cons _ _ _ (der_21850 v h) (by intro d hd; cases hd)))
def cl_22442 : CNF.NClause := [(86,true),(5,true),(1,false),(18,false),(14,false),(29,true)]
theorem der_22442 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22442 :=
  CNF.rup_sound cl_22442 [cl_1587,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1587 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22443 : CNF.NClause := [(86,true),(5,true),(1,false),(18,false),(14,true),(29,true)]
theorem der_22443 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22443 :=
  CNF.rup_sound cl_22443 [cl_1591,cl_19067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1591 v h) (hints_cons _ _ _ (der_19067 v h) (by intro d hd; cases hd)))
def cl_22444 : CNF.NClause := [(86,true),(1,false),(5,true),(14,false),(18,true),(29,true)]
theorem der_22444 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22444 :=
  CNF.rup_sound cl_22444 [cl_1595,cl_21850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1595 v h) (hints_cons _ _ _ (der_21850 v h) (by intro d hd; cases hd)))
def cl_22445 : CNF.NClause := [(85,true),(5,true),(3,false),(19,false),(21,false),(27,false)]
theorem der_22445 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22445 :=
  CNF.rup_sound cl_22445 [cl_1479,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1479 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22446 : CNF.NClause := [(85,true),(27,false),(5,true),(3,false),(12,false),(21,false)]
theorem der_22446 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22446 :=
  CNF.rup_sound cl_22446 [cl_1483,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1483 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22447 : CNF.NClause := [(85,true),(12,true),(5,true),(3,false),(21,false),(27,false)]
theorem der_22447 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22447 :=
  CNF.rup_sound cl_22447 [cl_1487,cl_22445] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1487 v h) (hints_cons _ _ _ (der_22445 v h) (by intro d hd; cases hd)))
def cl_22448 : CNF.NClause := [(85,true),(19,false),(5,true),(3,false),(27,false),(12,false)]
theorem der_22448 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22448 :=
  CNF.rup_sound cl_22448 [cl_1491,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1491 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22449 : CNF.NClause := [(85,true),(12,true),(5,true),(3,false),(19,false),(27,false)]
theorem der_22449 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22449 :=
  CNF.rup_sound cl_22449 [cl_1495,cl_22447] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1495 v h) (hints_cons _ _ _ (der_22447 v h) (by intro d hd; cases hd)))
def cl_22450 : CNF.NClause := [(85,true),(21,true),(5,true),(3,false),(19,true),(27,false)]
theorem der_22450 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22450 :=
  CNF.rup_sound cl_22450 [cl_1503,cl_20807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1503 v h) (hints_cons _ _ _ (der_20807 v h) (by intro d hd; cases hd)))
def cl_22451 : CNF.NClause := [(85,true),(19,false),(5,true),(3,false),(12,false),(21,false)]
theorem der_22451 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22451 :=
  CNF.rup_sound cl_22451 [cl_1507,cl_15190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1507 v h) (hints_cons _ _ _ (der_15190 v h) (by intro d hd; cases hd)))
def cl_22452 : CNF.NClause := [(85,true),(5,true),(21,false),(19,false),(12,true),(27,true)]
theorem der_22452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22452 :=
  CNF.rup_sound cl_22452 [cl_1511,cl_1512] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1511 v h) (hints_cons _ _ _ (inp_1512 v h) (by intro d hd; cases hd)))
def cl_22453 : CNF.NClause := [(85,true),(12,false),(5,true),(3,false),(21,true),(27,true)]
theorem der_22453 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22453 :=
  CNF.rup_sound cl_22453 [cl_1523,cl_20807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1523 v h) (hints_cons _ _ _ (der_20807 v h) (by intro d hd; cases hd)))
def cl_22454 : CNF.NClause := [(85,true),(5,true),(3,false),(19,false),(21,true),(27,true)]
theorem der_22454 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22454 :=
  CNF.rup_sound cl_22454 [cl_1527,cl_22453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1527 v h) (hints_cons _ _ _ (der_22453 v h) (by intro d hd; cases hd)))
def cl_22455 : CNF.NClause := [(30,false),(8,true),(5,true),(9,true),(82,true),(7,false)]
theorem der_22455 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22455 :=
  CNF.rup_sound cl_22455 [cl_1308,cl_15595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1308 v h) (hints_cons _ _ _ (der_15595 v h) (by intro d hd; cases hd)))
def cl_22456 : CNF.NClause := [(79,false),(15,true),(14,true),(2,true),(8,true),(21,true)]
theorem der_22456 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22456 :=
  CNF.rup_sound cl_22456 [cl_1120,cl_18884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1120 v h) (hints_cons _ _ _ (der_18884 v h) (by intro d hd; cases hd)))
def cl_22457 : CNF.NClause := [(79,false),(15,true),(14,true),(8,true),(26,true),(2,true)]
theorem der_22457 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22457 :=
  CNF.rup_sound cl_22457 [cl_1136,cl_18884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1136 v h) (hints_cons _ _ _ (der_18884 v h) (by intro d hd; cases hd)))
def cl_22458 : CNF.NClause := [(79,false),(15,true),(26,true),(8,true),(2,true),(21,true)]
theorem der_22458 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22458 :=
  CNF.rup_sound cl_22458 [cl_1148,cl_18884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1148 v h) (hints_cons _ _ _ (der_18884 v h) (by intro d hd; cases hd)))
def cl_22459 : CNF.NClause := [(79,false),(15,true),(14,true),(26,true),(21,true),(2,true)]
theorem der_22459 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22459 :=
  CNF.rup_sound cl_22459 [cl_1150,cl_18884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1150 v h) (hints_cons _ _ _ (der_18884 v h) (by intro d hd; cases hd)))
def cl_22460 : CNF.NClause := [(84,false),(2,true),(24,true),(5,true),(16,true),(13,true)]
theorem der_22460 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22460 :=
  CNF.rup_sound cl_22460 [cl_1440,cl_19228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1440 v h) (hints_cons _ _ _ (der_19228 v h) (by intro d hd; cases hd)))
def cl_22461 : CNF.NClause := [(84,false),(2,true),(13,true),(5,true),(24,true),(28,true)]
theorem der_22461 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22461 :=
  CNF.rup_sound cl_22461 [cl_1464,cl_19228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1464 v h) (hints_cons _ _ _ (der_19228 v h) (by intro d hd; cases hd)))
def cl_22462 : CNF.NClause := [(84,false),(28,true),(2,true),(13,true),(16,true),(24,true)]
theorem der_22462 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22462 :=
  CNF.rup_sound cl_22462 [cl_1470,cl_19228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1470 v h) (hints_cons _ _ _ (der_19228 v h) (by intro d hd; cases hd)))
def cl_22463 : CNF.NClause := [(84,false),(28,true),(5,true),(13,true),(24,true),(16,true)]
theorem der_22463 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22463 :=
  CNF.rup_sound cl_22463 [cl_1471,cl_19228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1471 v h) (hints_cons _ _ _ (der_19228 v h) (by intro d hd; cases hd)))
def cl_22464 : CNF.NClause := [(23,true),(74,false),(19,true),(6,true),(10,true),(2,true)]
theorem der_22464 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22464 :=
  CNF.rup_sound cl_22464 [cl_800,cl_20836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_800 v h) (hints_cons _ _ _ (der_20836 v h) (by intro d hd; cases hd)))
def cl_22465 : CNF.NClause := [(74,false),(2,true),(19,true),(6,true),(10,true),(29,true)]
theorem der_22465 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22465 :=
  CNF.rup_sound cl_22465 [cl_816,cl_20836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_816 v h) (hints_cons _ _ _ (der_20836 v h) (by intro d hd; cases hd)))
def cl_22466 : CNF.NClause := [(23,true),(2,true),(29,true),(6,true),(10,true),(74,false)]
theorem der_22466 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22466 :=
  CNF.rup_sound cl_22466 [cl_824,cl_20836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_824 v h) (hints_cons _ _ _ (der_20836 v h) (by intro d hd; cases hd)))
def cl_22467 : CNF.NClause := [(23,true),(2,true),(74,false),(6,true),(19,true),(29,true)]
theorem der_22467 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22467 :=
  CNF.rup_sound cl_22467 [cl_828,cl_20836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_828 v h) (hints_cons _ _ _ (der_20836 v h) (by intro d hd; cases hd)))
def cl_22468 : CNF.NClause := [(23,true),(74,false),(10,true),(29,true),(19,true),(2,true)]
theorem der_22468 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22468 :=
  CNF.rup_sound cl_22468 [cl_830,cl_20836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_830 v h) (hints_cons _ _ _ (der_20836 v h) (by intro d hd; cases hd)))
def cl_22469 : CNF.NClause := [(44,false),(72,true),(78,false),(65,false),(13,true),(88,false)]
theorem der_22469 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22469 :=
  CNF.rup_sound cl_22469 [cl_19649,cl_19645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19649 v h) (hints_cons _ _ _ (der_19645 v h) (by intro d hd; cases hd)))
def cl_22470 : CNF.NClause := [(41,false),(75,true),(92,false),(74,false),(10,true),(76,false)]
theorem der_22470 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22470 :=
  CNF.rup_sound cl_22470 [cl_20069,cl_20053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20069 v h) (hints_cons _ _ _ (der_20053 v h) (by intro d hd; cases hd)))
def cl_22471 : CNF.NClause := [(48,false),(88,false),(17,true),(77,false),(64,false),(70,false)]
theorem der_22471 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22471 :=
  CNF.rup_sound cl_22471 [cl_18281,cl_18279] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18281 v h) (hints_cons _ _ _ (der_18279 v h) (by intro d hd; cases hd)))
def cl_22472 : CNF.NClause := [(89,false),(14,true),(0,true),(16,true),(7,true),(23,true)]
theorem der_22472 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22472 :=
  CNF.rup_sound cl_22472 [cl_1760,cl_18273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1760 v h) (hints_cons _ _ _ (der_18273 v h) (by intro d hd; cases hd)))
def cl_22473 : CNF.NClause := [(89,false),(14,true),(0,true),(27,true),(7,true),(16,true)]
theorem der_22473 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22473 :=
  CNF.rup_sound cl_22473 [cl_1776,cl_18273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1776 v h) (hints_cons _ _ _ (der_18273 v h) (by intro d hd; cases hd)))
def cl_22474 : CNF.NClause := [(89,false),(16,true),(0,true),(7,true),(23,true),(27,true)]
theorem der_22474 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22474 :=
  CNF.rup_sound cl_22474 [cl_1788,cl_18273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1788 v h) (hints_cons _ _ _ (der_18273 v h) (by intro d hd; cases hd)))
def cl_22475 : CNF.NClause := [(89,false),(23,true),(14,true),(0,true),(16,true),(27,true)]
theorem der_22475 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22475 :=
  CNF.rup_sound cl_22475 [cl_1790,cl_18273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1790 v h) (hints_cons _ _ _ (der_18273 v h) (by intro d hd; cases hd)))
def cl_22476 : CNF.NClause := [(54,false),(74,false),(23,true),(83,false),(81,false),(67,false)]
theorem der_22476 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22476 :=
  CNF.rup_sound cl_22476 [cl_18275,cl_20035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18275 v h) (hints_cons _ _ _ (der_20035 v h) (by intro d hd; cases hd)))
def cl_22477 : CNF.NClause := [(54,false),(74,false),(65,true),(83,false),(81,false),(67,false)]
theorem der_22477 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22477 :=
  CNF.rup_sound cl_22477 [cl_18501,cl_20097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18501 v h) (hints_cons _ _ _ (der_20097 v h) (by intro d hd; cases hd)))
def cl_22478 : CNF.NClause := [(54,false),(81,true),(65,false),(67,false),(74,false),(83,false)]
theorem der_22478 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22478 :=
  CNF.rup_sound cl_22478 [cl_19909,cl_20097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19909 v h) (hints_cons _ _ _ (der_20097 v h) (by intro d hd; cases hd)))
def cl_22479 : CNF.NClause := [(88,false),(17,true),(0,true),(13,true),(9,true),(29,true)]
theorem der_22479 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22479 :=
  CNF.rup_sound cl_22479 [cl_1712,cl_19061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1712 v h) (hints_cons _ _ _ (der_19061 v h) (by intro d hd; cases hd)))
def cl_22480 : CNF.NClause := [(88,false),(9,true),(29,true),(21,true),(13,true),(0,true)]
theorem der_22480 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22480 :=
  CNF.rup_sound cl_22480 [cl_1720,cl_19061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1720 v h) (hints_cons _ _ _ (der_19061 v h) (by intro d hd; cases hd)))
def cl_22481 : CNF.NClause := [(88,false),(0,true),(17,true),(29,true),(9,true),(21,true)]
theorem der_22481 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22481 :=
  CNF.rup_sound cl_22481 [cl_1724,cl_19061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1724 v h) (hints_cons _ _ _ (der_19061 v h) (by intro d hd; cases hd)))
def cl_22482 : CNF.NClause := [(88,false),(13,true),(9,true),(29,true),(21,true),(17,true)]
theorem der_22482 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22482 :=
  CNF.rup_sound cl_22482 [cl_1727,cl_19061] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1727 v h) (hints_cons _ _ _ (der_19061 v h) (by intro d hd; cases hd)))
def cl_22483 : CNF.NClause := [(92,false),(20,true),(15,true),(10,true),(5,true),(0,true)]
theorem der_22483 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22483 :=
  CNF.rup_sound cl_22483 [cl_1952,cl_18125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1952 v h) (hints_cons _ _ _ (der_18125 v h) (by intro d hd; cases hd)))
def cl_22484 : CNF.NClause := [(92,false),(25,true),(5,true),(20,true),(10,true),(0,true)]
theorem der_22484 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22484 :=
  CNF.rup_sound cl_22484 [cl_1976,cl_18125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1976 v h) (hints_cons _ _ _ (der_18125 v h) (by intro d hd; cases hd)))
def cl_22485 : CNF.NClause := [(92,false),(20,true),(10,true),(0,true),(15,true),(25,true)]
theorem der_22485 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22485 :=
  CNF.rup_sound cl_22485 [cl_1982,cl_18125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1982 v h) (hints_cons _ _ _ (der_18125 v h) (by intro d hd; cases hd)))
def cl_22486 : CNF.NClause := [(92,false),(15,true),(20,true),(10,true),(5,true),(25,true)]
theorem der_22486 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22486 :=
  CNF.rup_sound cl_22486 [cl_1983,cl_18125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1983 v h) (hints_cons _ _ _ (der_18125 v h) (by intro d hd; cases hd)))
def cl_22487 : CNF.NClause := [(65,false),(23,true),(8,true),(25,true),(13,true),(18,true)]
theorem der_22487 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22487 :=
  CNF.rup_sound cl_22487 [cl_255,cl_18723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_255 v h) (hints_cons _ _ _ (der_18723 v h) (by intro d hd; cases hd)))
def cl_22488 : CNF.NClause := [(70,false),(14,true),(3,true),(20,true),(6,true),(17,true)]
theorem der_22488 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22488 :=
  CNF.rup_sound cl_22488 [cl_576,cl_544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_576 v h) (hints_cons _ _ _ (inp_544 v h) (by intro d hd; cases hd)))
def cl_22489 : CNF.NClause := [(59,false),(81,false),(28,true),(70,false),(90,false),(73,false)]
theorem der_22489 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22489 :=
  CNF.rup_sound cl_22489 [cl_20031,cl_19328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20031 v h) (hints_cons _ _ _ (der_19328 v h) (by intro d hd; cases hd)))
def cl_22491 : CNF.NClause := [(58,false),(27,true),(89,false),(76,false),(78,false),(69,false)]
theorem der_22491 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22491 :=
  CNF.rup_sound cl_22491 [cl_17873,cl_20395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17873 v h) (hints_cons _ _ _ (der_20395 v h) (by intro d hd; cases hd)))
def cl_22492 : CNF.NClause := [(58,false),(89,true),(27,true),(69,false),(76,false),(78,false)]
theorem der_22492 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22492 :=
  CNF.rup_sound cl_22492 [cl_19292,cl_20395] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19292 v h) (hints_cons _ _ _ (der_20395 v h) (by intro d hd; cases hd)))
def cl_22493 : CNF.NClause := [(52,false),(66,false),(21,true),(79,false),(67,false),(73,false)]
theorem der_22493 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22493 :=
  CNF.rup_sound cl_22493 [cl_18863,cl_22058] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_18863 v h) (hints_cons _ _ _ (der_22058 v h) (by intro d hd; cases hd)))
def cl_22496 : CNF.NClause := [(12,true),(91,false),(24,true),(6,true),(18,true),(0,true)]
theorem der_22496 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22496 :=
  CNF.rup_sound cl_22496 [cl_1888,cl_20803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1888 v h) (hints_cons _ _ _ (der_20803 v h) (by intro d hd; cases hd)))
def cl_22497 : CNF.NClause := [(91,false),(26,true),(0,true),(6,true),(12,true),(18,true)]
theorem der_22497 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22497 :=
  CNF.rup_sound cl_22497 [cl_1904,cl_20803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1904 v h) (hints_cons _ _ _ (der_20803 v h) (by intro d hd; cases hd)))
def cl_22498 : CNF.NClause := [(12,true),(24,true),(26,true),(91,false),(0,true),(18,true)]
theorem der_22498 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22498 :=
  CNF.rup_sound cl_22498 [cl_1918,cl_20803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1918 v h) (hints_cons _ _ _ (der_20803 v h) (by intro d hd; cases hd)))
def cl_22499 : CNF.NClause := [(12,true),(6,true),(91,false),(24,true),(26,true),(18,true)]
theorem der_22499 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22499 :=
  CNF.rup_sound cl_22499 [cl_1919,cl_20803] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1919 v h) (hints_cons _ _ _ (der_20803 v h) (by intro d hd; cases hd)))
def cl_22500 : CNF.NClause := [(89,true),(0,false),(16,false),(23,false),(7,false),(14,false)]
theorem der_22500 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22500 :=
  CNF.rup_sound cl_22500 [cl_1761,cl_15187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1761 v h) (hints_cons _ _ _ (der_15187 v h) (by intro d hd; cases hd)))
def cl_22501 : CNF.NClause := [(3,true),(87,false),(1,true),(4,true),(2,true),(30,true)]
theorem der_22501 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22501 :=
  CNF.rup_sound cl_22501 [cl_1663,cl_19305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1663 v h) (hints_cons _ _ _ (der_19305 v h) (by intro d hd; cases hd)))
def cl_22503 : CNF.NClause := [(87,true),(0,false),(1,true),(2,true),(3,false),(4,true)]
theorem der_22503 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22503 :=
  CNF.rup_sound cl_22503 [cl_1655,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1655 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22504 : CNF.NClause := [(87,true),(0,false),(1,true),(2,false),(3,false),(4,true)]
theorem der_22504 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22504 :=
  CNF.rup_sound cl_22504 [cl_1651,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1651 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22505 : CNF.NClause := [(25,false),(5,true),(92,true),(15,true),(0,false),(20,false)]
theorem der_22505 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22505 :=
  CNF.rup_sound cl_22505 [cl_1931,cl_21918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1931 v h) (hints_cons _ _ _ (der_21918 v h) (by intro d hd; cases hd)))
def cl_22506 : CNF.NClause := [(20,true),(5,true),(92,true),(15,false),(0,false),(25,false)]
theorem der_22506 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22506 :=
  CNF.rup_sound cl_22506 [cl_1939,cl_21918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1939 v h) (hints_cons _ _ _ (der_21918 v h) (by intro d hd; cases hd)))
def cl_22507 : CNF.NClause := [(20,true),(5,true),(92,true),(15,true),(0,false),(25,false)]
theorem der_22507 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22507 :=
  CNF.rup_sound cl_22507 [cl_1947,cl_21918] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1947 v h) (hints_cons _ _ _ (der_21918 v h) (by intro d hd; cases hd)))
def cl_22508 : CNF.NClause := [(10,false),(25,true),(5,true),(92,true),(15,false),(20,false)]
theorem der_22508 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22508 :=
  CNF.rup_sound cl_22508 [cl_1955,cl_21912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1955 v h) (hints_cons _ _ _ (der_21912 v h) (by intro d hd; cases hd)))
def cl_22510 : CNF.NClause := [(15,true),(5,true),(92,true),(20,false),(0,false),(25,true)]
theorem der_22510 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22510 :=
  CNF.rup_sound cl_22510 [cl_1963,cl_19353] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1963 v h) (hints_cons _ _ _ (der_19353 v h) (by intro d hd; cases hd)))
def cl_22511 : CNF.NClause := [(10,false),(25,true),(5,true),(92,true),(15,false),(20,true)]
theorem der_22511 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22511 :=
  CNF.rup_sound cl_22511 [cl_1971,cl_21912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1971 v h) (hints_cons _ _ _ (der_21912 v h) (by intro d hd; cases hd)))
def cl_22512 : CNF.NClause := [(10,false),(25,true),(5,true),(92,true),(0,false),(20,true)]
theorem der_22512 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22512 :=
  CNF.rup_sound cl_22512 [cl_1979,cl_22511] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1979 v h) (hints_cons _ _ _ (der_22511 v h) (by intro d hd; cases hd)))
def cl_22513 : CNF.NClause := [(3,true),(7,true),(24,true),(11,true),(15,true),(80,false)]
theorem der_22513 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22513 :=
  CNF.rup_sound cl_22513 [cl_1184,cl_20449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1184 v h) (hints_cons _ _ _ (der_20449 v h) (by intro d hd; cases hd)))
def cl_22514 : CNF.NClause := [(80,false),(15,true),(11,true),(3,true),(7,true),(29,true)]
theorem der_22514 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22514 :=
  CNF.rup_sound cl_22514 [cl_1200,cl_20449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1200 v h) (hints_cons _ _ _ (der_20449 v h) (by intro d hd; cases hd)))
def cl_22515 : CNF.NClause := [(80,false),(3,true),(24,true),(7,true),(11,true),(29,true)]
theorem der_22515 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22515 :=
  CNF.rup_sound cl_22515 [cl_1208,cl_20449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1208 v h) (hints_cons _ _ _ (der_20449 v h) (by intro d hd; cases hd)))
def cl_22516 : CNF.NClause := [(80,false),(15,true),(3,true),(24,true),(11,true),(29,true)]
theorem der_22516 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22516 :=
  CNF.rup_sound cl_22516 [cl_1214,cl_20449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1214 v h) (hints_cons _ _ _ (der_20449 v h) (by intro d hd; cases hd)))
def cl_22517 : CNF.NClause := [(80,false),(15,true),(24,true),(11,true),(7,true),(29,true)]
theorem der_22517 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22517 :=
  CNF.rup_sound cl_22517 [cl_1215,cl_20449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1215 v h) (hints_cons _ _ _ (der_20449 v h) (by intro d hd; cases hd)))
def cl_22518 : CNF.NClause := [(42,false),(69,true),(66,false),(90,false),(83,false),(11,true)]
theorem der_22518 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22518 :=
  CNF.rup_sound cl_22518 [cl_19483,cl_19489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19483 v h) (hints_cons _ _ _ (der_19489 v h) (by intro d hd; cases hd)))
def cl_22519 : CNF.NClause := [(42,false),(83,true),(72,false),(66,false),(90,false),(80,false)]
theorem der_22519 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22519 :=
  CNF.rup_sound cl_22519 [cl_17978,cl_19497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_17978 v h) (hints_cons _ _ _ (der_19497 v h) (by intro d hd; cases hd)))
def cl_22521 : CNF.NClause := [(50,false),(90,false),(85,true),(77,false),(19,true),(71,false)]
theorem der_22521 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22521 :=
  CNF.rup_sound cl_22521 [cl_20524,cl_19481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20524 v h) (hints_cons _ _ _ (der_19481 v h) (by intro d hd; cases hd)))
def cl_22522 : CNF.NClause := [(49,false),(73,false),(18,true),(65,false),(91,false),(77,false)]
theorem der_22522 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22522 :=
  CNF.rup_sound cl_22522 [cl_21576,cl_21548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_21576 v h) (hints_cons _ _ _ (der_21548 v h) (by intro d hd; cases hd)))
def cl_22523 : CNF.NClause := [(95,true),(38,false),(56,false),(33,false),(48,true),(43,true)]
theorem der_22523 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22523 :=
  CNF.rup_sound cl_22523 [cl_2141,cl_2125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2141 v h) (hints_cons _ _ _ (inp_2125 v h) (by intro d hd; cases hd)))
def cl_22524 : CNF.NClause := [(95,true),(43,true),(48,true),(33,false),(38,false),(53,false)]
theorem der_22524 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22524 :=
  CNF.rup_sound cl_22524 [cl_2157,cl_22523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2157 v h) (hints_cons _ _ _ (der_22523 v h) (by intro d hd; cases hd)))
def cl_22525 : CNF.NClause := [(95,true),(43,true),(48,true),(33,false),(38,false),(53,true)]
theorem der_22525 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22525 :=
  CNF.rup_sound cl_22525 [cl_2173,cl_22523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2173 v h) (hints_cons _ _ _ (der_22523 v h) (by intro d hd; cases hd)))
def cl_22526 : CNF.NClause := [(116,true),(36,false),(52,true),(34,false),(50,false),(43,true)]
theorem der_22526 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22526 :=
  CNF.rup_sound cl_22526 [cl_3509,cl_3477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3509 v h) (hints_cons _ _ _ (inp_3477 v h) (by intro d hd; cases hd)))
def cl_22527 : CNF.NClause := [(116,true),(36,false),(52,true),(50,false),(43,true),(58,false)]
theorem der_22527 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22527 :=
  CNF.rup_sound cl_22527 [cl_3478,cl_3477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3478 v h) (hints_cons _ _ _ (inp_3477 v h) (by intro d hd; cases hd)))
def cl_22528 : CNF.NClause := [(116,true),(36,false),(43,true),(50,false),(52,false),(58,true)]
theorem der_22528 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22528 :=
  CNF.rup_sound cl_22528 [cl_3494,cl_3493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3494 v h) (hints_cons _ _ _ (inp_3493 v h) (by intro d hd; cases hd)))
def cl_22529 : CNF.NClause := [(116,true),(36,false),(52,true),(50,false),(43,true),(58,true)]
theorem der_22529 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22529 :=
  CNF.rup_sound cl_22529 [cl_3510,cl_22526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3510 v h) (hints_cons _ _ _ (der_22526 v h) (by intro d hd; cases hd)))
def cl_22530 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true)]
theorem der_22530 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22530 :=
  CNF.rup_sound cl_22530 [cl_3904,cl_3872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3904 v h) (hints_cons _ _ _ (inp_3872 v h) (by intro d hd; cases hd)))
def cl_22531 : CNF.NClause := [(122,true),(31,false),(37,true),(43,true),(55,false),(57,false)]
theorem der_22531 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22531 :=
  CNF.rup_sound cl_22531 [cl_3855,cl_21935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3855 v h) (hints_cons _ _ _ (der_21935 v h) (by intro d hd; cases hd)))
def cl_22532 : CNF.NClause := [(122,true),(31,false),(49,true),(37,true),(43,true),(57,false)]
theorem der_22532 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22532 :=
  CNF.rup_sound cl_22532 [cl_3871,cl_22531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3871 v h) (hints_cons _ _ _ (der_22531 v h) (by intro d hd; cases hd)))
def cl_22533 : CNF.NClause := [(122,true),(31,false),(57,true),(37,true),(55,false),(43,true)]
theorem der_22533 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22533 :=
  CNF.rup_sound cl_22533 [cl_3887,cl_21935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3887 v h) (hints_cons _ _ _ (der_21935 v h) (by intro d hd; cases hd)))
def cl_22534 : CNF.NClause := [(122,false),(55,true),(37,true),(43,true),(57,true),(49,true)]
theorem der_22534 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22534 :=
  CNF.rup_sound cl_22534 [cl_3903,cl_22530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3903 v h) (hints_cons _ _ _ (der_22530 v h) (by intro d hd; cases hd)))
def cl_22535 : CNF.NClause := [(122,true),(43,true),(57,false),(49,true),(37,true),(55,false)]
theorem der_22535 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22535 :=
  CNF.rup_sound cl_22535 [cl_3856,cl_22531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3856 v h) (hints_cons _ _ _ (der_22531 v h) (by intro d hd; cases hd)))
def cl_22536 : CNF.NClause := [(112,true),(59,false),(43,true),(46,false),(40,false),(54,true)]
theorem der_22536 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22536 :=
  CNF.rup_sound cl_22536 [cl_3221,cl_17958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3221 v h) (hints_cons _ _ _ (der_17958 v h) (by intro d hd; cases hd)))
def cl_22537 : CNF.NClause := [(32,false),(112,true),(54,true),(43,true),(46,false),(59,true)]
theorem der_22537 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22537 :=
  CNF.rup_sound cl_22537 [cl_3253,cl_19282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3253 v h) (hints_cons _ _ _ (der_19282 v h) (by intro d hd; cases hd)))
def cl_22538 : CNF.NClause := [(116,true),(36,false),(34,false),(43,false),(50,false),(58,false)]
theorem der_22538 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22538 :=
  CNF.rup_sound cl_22538 [cl_3473,cl_15173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3473 v h) (hints_cons _ _ _ (der_15173 v h) (by intro d hd; cases hd)))
def cl_22539 : CNF.NClause := [(116,true),(50,false),(43,false),(36,true),(58,false),(34,false)]
theorem der_22539 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22539 :=
  CNF.rup_sound cl_22539 [cl_3475,cl_15173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3475 v h) (hints_cons _ _ _ (der_15173 v h) (by intro d hd; cases hd)))
def cl_22540 : CNF.NClause := [(46,false),(78,false),(92,false),(15,true),(81,false),(77,false)]
theorem der_22540 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22540 :=
  CNF.rup_sound cl_22540 [cl_19279,cl_19270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19279 v h) (hints_cons _ _ _ (der_19270 v h) (by intro d hd; cases hd)))
def cl_22541 : CNF.NClause := [(2,true),(3,true),(1,true),(0,true),(87,false),(30,true)]
theorem der_22541 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22541 :=
  CNF.rup_sound cl_22541 [cl_1648,cl_19305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1648 v h) (hints_cons _ _ _ (der_19305 v h) (by intro d hd; cases hd)))
def cl_22542 : CNF.NClause := [(87,false),(2,true),(1,true),(0,true),(4,true),(30,true)]
theorem der_22542 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22542 :=
  CNF.rup_sound cl_22542 [cl_1656,cl_19305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1656 v h) (hints_cons _ _ _ (der_19305 v h) (by intro d hd; cases hd)))
def cl_22543 : CNF.NClause := [(87,false),(3,true),(2,true),(4,true),(0,true),(30,true)]
theorem der_22543 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22543 :=
  CNF.rup_sound cl_22543 [cl_1662,cl_19305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1662 v h) (hints_cons _ _ _ (der_19305 v h) (by intro d hd; cases hd)))
def cl_22544 : CNF.NClause := [(34,false),(75,true),(65,false),(3,true),(70,false),(87,false)]
theorem der_22544 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22544 :=
  CNF.rup_sound cl_22544 [cl_19992,cl_19590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19992 v h) (hints_cons _ _ _ (der_19590 v h) (by intro d hd; cases hd)))
def cl_22545 : CNF.NClause := [(99,true),(60,false),(35,false),(47,true),(51,false),(39,true)]
theorem der_22545 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22545 :=
  CNF.rup_sound cl_22545 [cl_2379,cl_17834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2379 v h) (hints_cons _ _ _ (der_17834 v h) (by intro d hd; cases hd)))
def cl_22546 : CNF.NClause := [(99,true),(60,false),(35,false),(43,false),(47,true),(39,true)]
theorem der_22546 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22546 :=
  CNF.rup_sound cl_22546 [cl_2395,cl_22545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2395 v h) (hints_cons _ _ _ (der_22545 v h) (by intro d hd; cases hd)))
def cl_22547 : CNF.NClause := [(99,true),(35,false),(51,false),(47,true),(60,true),(39,true)]
theorem der_22547 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22547 :=
  CNF.rup_sound cl_22547 [cl_2411,cl_17834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2411 v h) (hints_cons _ _ _ (der_17834 v h) (by intro d hd; cases hd)))
def cl_22548 : CNF.NClause := [(99,true),(35,false),(47,true),(39,true),(43,false),(51,true)]
theorem der_22548 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22548 :=
  CNF.rup_sound cl_22548 [cl_2427,cl_22546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2427 v h) (hints_cons _ _ _ (der_22546 v h) (by intro d hd; cases hd)))
def cl_22549 : CNF.NClause := [(99,true),(60,false),(43,true),(39,true),(47,true),(35,false)]
theorem der_22549 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22549 :=
  CNF.rup_sound cl_22549 [cl_2399,cl_17834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2399 v h) (hints_cons _ _ _ (der_17834 v h) (by intro d hd; cases hd)))
def cl_22550 : CNF.NClause := [(99,true),(35,false),(39,true),(43,true),(60,true),(51,false)]
theorem der_22550 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22550 :=
  CNF.rup_sound cl_22550 [cl_2407,cl_17834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2407 v h) (hints_cons _ _ _ (der_17834 v h) (by intro d hd; cases hd)))
def cl_22551 : CNF.NClause := [(32,false),(76,true),(66,false),(71,false),(81,false),(86,false)]
theorem der_22551 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22551 :=
  CNF.rup_sound cl_22551 [cl_19250,cl_19254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19250 v h) (hints_cons _ _ _ (der_19254 v h) (by intro d hd; cases hd)))
def cl_22552 : CNF.NClause := [(32,false),(112,true),(43,false),(46,false),(54,false),(59,true)]
theorem der_22552 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22552 :=
  CNF.rup_sound cl_22552 [cl_3233,cl_20324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3233 v h) (hints_cons _ _ _ (der_20324 v h) (by intro d hd; cases hd)))
def cl_22553 : CNF.NClause := [(112,true),(32,false),(43,true),(59,false),(40,true),(46,true)]
theorem der_22553 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22553 :=
  CNF.rup_sound cl_22553 [cl_3231,cl_19153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3231 v h) (hints_cons _ _ _ (der_19153 v h) (by intro d hd; cases hd)))
def cl_22554 : CNF.NClause := [(32,false),(112,true),(43,false),(40,false),(54,false),(59,false)]
theorem der_22554 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22554 :=
  CNF.rup_sound cl_22554 [cl_3209,cl_21994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3209 v h) (hints_cons _ _ _ (der_21994 v h) (by intro d hd; cases hd)))
def cl_22555 : CNF.NClause := [(32,false),(112,true),(59,false),(43,false),(40,false),(54,true)]
theorem der_22555 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22555 :=
  CNF.rup_sound cl_22555 [cl_3225,cl_15238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3225 v h) (hints_cons _ _ _ (der_15238 v h) (by intro d hd; cases hd)))
def cl_22556 : CNF.NClause := [(32,false),(112,true),(46,true),(43,false),(40,false),(54,false)]
theorem der_22556 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22556 :=
  CNF.rup_sound cl_22556 [cl_3241,cl_22554] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3241 v h) (hints_cons _ _ _ (der_22554 v h) (by intro d hd; cases hd)))
def cl_22557 : CNF.NClause := [(32,false),(112,true),(59,true),(43,false),(40,false),(46,true)]
theorem der_22557 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22557 :=
  CNF.rup_sound cl_22557 [cl_3257,cl_22556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3257 v h) (hints_cons _ _ _ (der_22556 v h) (by intro d hd; cases hd)))
def cl_22558 : CNF.NClause := [(32,false),(112,true),(40,true),(59,false),(54,false),(43,false)]
theorem der_22558 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22558 :=
  CNF.rup_sound cl_22558 [cl_3211,cl_22014] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3211 v h) (hints_cons _ _ _ (der_22014 v h) (by intro d hd; cases hd)))
def cl_22559 : CNF.NClause := [(32,false),(112,true),(40,true),(43,false),(46,true),(59,false)]
theorem der_22559 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22559 :=
  CNF.rup_sound cl_22559 [cl_3227,cl_22558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3227 v h) (hints_cons _ _ _ (der_22558 v h) (by intro d hd; cases hd)))
def cl_22560 : CNF.NClause := [(32,false),(112,true),(40,true),(46,true),(54,false),(43,false)]
theorem der_22560 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22560 :=
  CNF.rup_sound cl_22560 [cl_3243,cl_22559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3243 v h) (hints_cons _ _ _ (der_22559 v h) (by intro d hd; cases hd)))
def cl_22561 : CNF.NClause := [(32,false),(112,true),(43,false),(40,true),(46,true),(54,true)]
theorem der_22561 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22561 :=
  CNF.rup_sound cl_22561 [cl_3259,cl_22559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3259 v h) (hints_cons _ _ _ (der_22559 v h) (by intro d hd; cases hd)))
def cl_22562 : CNF.NClause := [(10,false),(22,false),(3,false),(26,true),(16,false),(75,true)]
theorem der_22562 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22562 :=
  CNF.rup_sound cl_22562 [cl_865,cl_17644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_865 v h) (hints_cons _ _ _ (der_17644 v h) (by intro d hd; cases hd)))
def cl_22563 : CNF.NClause := [(87,true),(0,false),(3,false),(1,false),(2,false),(4,true)]
theorem der_22563 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22563 :=
  CNF.rup_sound cl_22563 [cl_1649,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1649 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22564 : CNF.NClause := [(87,true),(1,false),(0,true),(2,false),(3,false),(4,true)]
theorem der_22564 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22564 :=
  CNF.rup_sound cl_22564 [cl_1650,cl_15147] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1650 v h) (hints_cons _ _ _ (der_15147 v h) (by intro d hd; cases hd)))
def cl_22565 : CNF.NClause := [(84,true),(5,false),(24,false),(2,false),(13,false),(16,false)]
theorem der_22565 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22565 :=
  CNF.rup_sound cl_22565 [cl_1441,cl_15185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1441 v h) (hints_cons _ _ _ (der_15185 v h) (by intro d hd; cases hd)))
def cl_22566 : CNF.NClause := [(11,false),(20,false),(9,true),(69,true),(2,false),(18,true)]
theorem der_22566 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22566 :=
  CNF.rup_sound cl_22566 [cl_459,cl_17996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_459 v h) (hints_cons _ _ _ (der_17996 v h) (by intro d hd; cases hd)))
def cl_22567 : CNF.NClause := [(10,false),(2,false),(29,false),(74,true),(19,true),(23,false)]
theorem der_22567 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22567 :=
  CNF.rup_sound cl_22567 [cl_777,cl_20704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_777 v h) (hints_cons _ _ _ (der_20704 v h) (by intro d hd; cases hd)))
def cl_22568 : CNF.NClause := [(10,false),(2,false),(29,false),(19,true),(74,true),(23,true)]
theorem der_22568 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22568 :=
  CNF.rup_sound cl_22568 [cl_793,cl_20704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_793 v h) (hints_cons _ _ _ (der_20704 v h) (by intro d hd; cases hd)))
def cl_22569 : CNF.NClause := [(10,false),(6,false),(2,false),(29,true),(19,true),(74,true)]
theorem der_22569 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22569 :=
  CNF.rup_sound cl_22569 [cl_825,cl_20550] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_825 v h) (hints_cons _ _ _ (der_20550 v h) (by intro d hd; cases hd)))
def cl_22570 : CNF.NClause := [(27,false),(10,false),(1,false),(8,false),(24,false),(76,true)]
theorem der_22570 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22570 :=
  CNF.rup_sound cl_22570 [cl_905,cl_22154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_905 v h) (hints_cons _ _ _ (der_22154 v h) (by intro d hd; cases hd)))
def cl_22571 : CNF.NClause := [(10,false),(76,true),(1,false),(8,false),(27,false),(17,true)]
theorem der_22571 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22571 :=
  CNF.rup_sound cl_22571 [cl_921,cl_22570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_921 v h) (hints_cons _ _ _ (der_22570 v h) (by intro d hd; cases hd)))
def cl_22572 : CNF.NClause := [(76,true),(1,false),(8,false),(17,true),(24,false),(27,true)]
theorem der_22572 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22572 :=
  CNF.rup_sound cl_22572 [cl_937,cl_20537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_937 v h) (hints_cons _ _ _ (der_20537 v h) (by intro d hd; cases hd)))
def cl_22573 : CNF.NClause := [(76,true),(1,false),(8,false),(17,true),(24,true),(27,true)]
theorem der_22573 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22573 :=
  CNF.rup_sound cl_22573 [cl_953,cl_20537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_953 v h) (hints_cons _ _ _ (der_20537 v h) (by intro d hd; cases hd)))
def cl_22574 : CNF.NClause := [(21,false),(10,false),(4,false),(73,true),(18,true),(28,false)]
theorem der_22574 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22574 :=
  CNF.rup_sound cl_22574 [cl_713,cl_22198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_713 v h) (hints_cons _ _ _ (der_22198 v h) (by intro d hd; cases hd)))
def cl_22575 : CNF.NClause := [(10,false),(73,true),(4,false),(18,true),(21,true),(28,false)]
theorem der_22575 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22575 :=
  CNF.rup_sound cl_22575 [cl_729,cl_22206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_729 v h) (hints_cons _ _ _ (der_22206 v h) (by intro d hd; cases hd)))
def cl_22576 : CNF.NClause := [(21,false),(10,false),(4,false),(7,false),(73,true),(18,true)]
theorem der_22576 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22576 :=
  CNF.rup_sound cl_22576 [cl_745,cl_22574] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_745 v h) (hints_cons _ _ _ (der_22574 v h) (by intro d hd; cases hd)))
def cl_22577 : CNF.NClause := [(10,false),(4,false),(18,true),(73,true),(21,true),(28,true)]
theorem der_22577 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22577 :=
  CNF.rup_sound cl_22577 [cl_761,cl_22206] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_761 v h) (hints_cons _ _ _ (der_22206 v h) (by intro d hd; cases hd)))
def cl_22578 : CNF.NClause := [(6,false),(19,false),(74,true),(29,true),(2,false),(23,false)]
theorem der_22578 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22578 :=
  CNF.rup_sound cl_22578 [cl_801,cl_21864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_801 v h) (hints_cons _ _ _ (der_21864 v h) (by intro d hd; cases hd)))
def cl_22579 : CNF.NClause := [(2,false),(23,false),(74,true),(19,true),(29,false),(6,true)]
theorem der_22579 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22579 :=
  CNF.rup_sound cl_22579 [cl_779,cl_21861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_779 v h) (hints_cons _ _ _ (der_21861 v h) (by intro d hd; cases hd)))
def cl_22580 : CNF.NClause := [(10,false),(19,false),(2,false),(74,true),(6,true),(29,false)]
theorem der_22580 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22580 :=
  CNF.rup_sound cl_22580 [cl_787,cl_15412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_787 v h) (hints_cons _ _ _ (der_15412 v h) (by intro d hd; cases hd)))
def cl_22581 : CNF.NClause := [(10,false),(19,false),(2,false),(74,true),(6,true),(23,false)]
theorem der_22581 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22581 :=
  CNF.rup_sound cl_22581 [cl_803,cl_15412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_803 v h) (hints_cons _ _ _ (der_15412 v h) (by intro d hd; cases hd)))
def cl_22582 : CNF.NClause := [(10,false),(19,false),(2,false),(74,true),(6,true),(23,true)]
theorem der_22582 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22582 :=
  CNF.rup_sound cl_22582 [cl_819,cl_22580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_819 v h) (hints_cons _ _ _ (der_22580 v h) (by intro d hd; cases hd)))
def cl_22583 : CNF.NClause := [(10,false),(23,true),(2,false),(74,true),(6,true),(29,true)]
theorem der_22583 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22583 :=
  CNF.rup_sound cl_22583 [cl_827,cl_22582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_827 v h) (hints_cons _ _ _ (der_22582 v h) (by intro d hd; cases hd)))
def cl_22584 : CNF.NClause := [(30,false),(13,false),(14,false),(11,false),(72,true),(10,false)]
theorem der_22584 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22584 :=
  CNF.rup_sound cl_22584 [cl_641,cl_15555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_641 v h) (hints_cons _ _ _ (der_15555 v h) (by intro d hd; cases hd)))
def cl_22585 : CNF.NClause := [(82,false),(8,true),(30,true),(5,true),(7,true),(6,true)]
theorem der_22585 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22585 :=
  CNF.rup_sound cl_22585 [cl_1328,cl_20821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1328 v h) (hints_cons _ _ _ (der_20821 v h) (by intro d hd; cases hd)))
def cl_22586 : CNF.NClause := [(82,false),(9,true),(30,true),(6,true),(5,true),(8,true)]
theorem der_22586 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22586 :=
  CNF.rup_sound cl_22586 [cl_1340,cl_20821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1340 v h) (hints_cons _ _ _ (der_20821 v h) (by intro d hd; cases hd)))
def cl_22587 : CNF.NClause := [(96,true),(49,false),(34,false),(56,false),(44,true),(54,false)]
theorem der_22587 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22587 :=
  CNF.rup_sound cl_22587 [cl_2181,cl_19189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2181 v h) (hints_cons _ _ _ (der_19189 v h) (by intro d hd; cases hd)))
def cl_22588 : CNF.NClause := [(96,true),(34,false),(54,false),(39,false),(56,false),(44,true)]
theorem der_22588 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22588 :=
  CNF.rup_sound cl_22588 [cl_2189,cl_22587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2189 v h) (hints_cons _ _ _ (der_22587 v h) (by intro d hd; cases hd)))
def cl_22589 : CNF.NClause := [(96,true),(49,false),(34,false),(44,true),(39,false),(56,false)]
theorem der_22589 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22589 :=
  CNF.rup_sound cl_22589 [cl_2197,cl_22587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2197 v h) (hints_cons _ _ _ (der_22587 v h) (by intro d hd; cases hd)))
def cl_22590 : CNF.NClause := [(96,true),(34,false),(39,false),(44,true),(49,true),(56,false)]
theorem der_22590 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22590 :=
  CNF.rup_sound cl_22590 [cl_2205,cl_22588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2205 v h) (hints_cons _ _ _ (der_22588 v h) (by intro d hd; cases hd)))
def cl_22591 : CNF.NClause := [(96,true),(49,false),(54,false),(34,false),(44,true),(56,true)]
theorem der_22591 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22591 :=
  CNF.rup_sound cl_22591 [cl_2213,cl_19189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2213 v h) (hints_cons _ _ _ (der_19189 v h) (by intro d hd; cases hd)))
def cl_22592 : CNF.NClause := [(96,true),(34,false),(54,false),(49,true),(39,false),(44,true)]
theorem der_22592 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22592 :=
  CNF.rup_sound cl_22592 [cl_2221,cl_22590] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2221 v h) (hints_cons _ _ _ (der_22590 v h) (by intro d hd; cases hd)))
def cl_22593 : CNF.NClause := [(96,true),(49,false),(56,true),(39,false),(34,false),(44,true)]
theorem der_22593 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22593 :=
  CNF.rup_sound cl_22593 [cl_2229,cl_22591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2229 v h) (hints_cons _ _ _ (der_22591 v h) (by intro d hd; cases hd)))
def cl_22594 : CNF.NClause := [(96,true),(34,false),(49,true),(39,false),(56,true),(44,true)]
theorem der_22594 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22594 :=
  CNF.rup_sound cl_22594 [cl_2237,cl_22592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2237 v h) (hints_cons _ _ _ (der_22592 v h) (by intro d hd; cases hd)))
def cl_22595 : CNF.NClause := [(96,true),(49,false),(34,true),(56,false),(44,true),(54,false)]
theorem der_22595 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22595 :=
  CNF.rup_sound cl_22595 [cl_2182,cl_19189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2182 v h) (hints_cons _ _ _ (der_19189 v h) (by intro d hd; cases hd)))
def cl_22596 : CNF.NClause := [(96,true),(54,false),(56,false),(49,true),(44,true),(39,false)]
theorem der_22596 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22596 :=
  CNF.rup_sound cl_22596 [cl_2190,cl_22592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2190 v h) (hints_cons _ _ _ (der_22592 v h) (by intro d hd; cases hd)))
def cl_22597 : CNF.NClause := [(96,true),(49,false),(34,true),(44,true),(39,false),(56,false)]
theorem der_22597 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22597 :=
  CNF.rup_sound cl_22597 [cl_2198,cl_22595] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2198 v h) (hints_cons _ _ _ (der_22595 v h) (by intro d hd; cases hd)))
def cl_22598 : CNF.NClause := [(96,true),(34,true),(56,false),(44,true),(39,false),(54,true)]
theorem der_22598 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22598 :=
  CNF.rup_sound cl_22598 [cl_2206,cl_22597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2206 v h) (hints_cons _ _ _ (der_22597 v h) (by intro d hd; cases hd)))
def cl_22599 : CNF.NClause := [(96,true),(49,false),(34,true),(54,false),(44,true),(56,true)]
theorem der_22599 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22599 :=
  CNF.rup_sound cl_22599 [cl_2214,cl_19189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2214 v h) (hints_cons _ _ _ (der_19189 v h) (by intro d hd; cases hd)))
def cl_22600 : CNF.NClause := [(96,true),(49,true),(39,false),(54,false),(44,true),(56,true)]
theorem der_22600 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22600 :=
  CNF.rup_sound cl_22600 [cl_2222,cl_22592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2222 v h) (hints_cons _ _ _ (der_22592 v h) (by intro d hd; cases hd)))
def cl_22601 : CNF.NClause := [(96,true),(49,false),(34,true),(39,false),(56,true),(44,true)]
theorem der_22601 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22601 :=
  CNF.rup_sound cl_22601 [cl_2230,cl_22599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2230 v h) (hints_cons _ _ _ (der_22599 v h) (by intro d hd; cases hd)))
def cl_22602 : CNF.NClause := [(99,true),(60,false),(35,false),(43,false),(39,false),(51,false)]
theorem der_22602 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22602 :=
  CNF.rup_sound cl_22602 [cl_2377,cl_14913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2377 v h) (hints_cons _ _ _ (der_14913 v h) (by intro d hd; cases hd)))
def cl_22603 : CNF.NClause := [(99,true),(60,false),(35,false),(43,false),(47,true),(39,false)]
theorem der_22603 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22603 :=
  CNF.rup_sound cl_22603 [cl_2393,cl_22602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2393 v h) (hints_cons _ _ _ (der_22602 v h) (by intro d hd; cases hd)))
def cl_22604 : CNF.NClause := [(99,true),(51,false),(35,false),(43,false),(47,true),(39,false)]
theorem der_22604 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22604 :=
  CNF.rup_sound cl_22604 [cl_2409,cl_22602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2409 v h) (hints_cons _ _ _ (der_22602 v h) (by intro d hd; cases hd)))
def cl_22605 : CNF.NClause := [(99,true),(35,false),(43,false),(47,true),(39,false),(60,true)]
theorem der_22605 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22605 :=
  CNF.rup_sound cl_22605 [cl_2425,cl_22604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2425 v h) (hints_cons _ _ _ (der_22604 v h) (by intro d hd; cases hd)))
def cl_22606 : CNF.NClause := [(121,true),(31,false),(42,true),(39,false),(50,false),(59,false)]
theorem der_22606 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22606 :=
  CNF.rup_sound cl_22606 [cl_3781,cl_20030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3781 v h) (hints_cons _ _ _ (der_20030 v h) (by intro d hd; cases hd)))
def cl_22607 : CNF.NClause := [(121,true),(50,false),(31,false),(39,false),(59,false),(53,false)]
theorem der_22607 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22607 :=
  CNF.rup_sound cl_22607 [cl_3777,cl_22606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3777 v h) (hints_cons _ _ _ (der_22606 v h) (by intro d hd; cases hd)))
def cl_22608 : CNF.NClause := [(113,true),(37,false),(36,true),(38,false),(39,false),(61,true)]
theorem der_22608 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22608 :=
  CNF.rup_sound cl_22608 [cl_3314,cl_3298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3314 v h) (hints_cons _ _ _ (inp_3298 v h) (by intro d hd; cases hd)))
def cl_22609 : CNF.NClause := [(96,true),(49,false),(54,false),(39,false),(34,false),(56,false)]
theorem der_22609 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22609 :=
  CNF.rup_sound cl_22609 [cl_2177,cl_22587] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2177 v h) (hints_cons _ _ _ (der_22587 v h) (by intro d hd; cases hd)))
def cl_22610 : CNF.NClause := [(96,true),(44,false),(56,false),(49,false),(54,false),(34,true)]
theorem der_22610 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22610 :=
  CNF.rup_sound cl_22610 [cl_2178,cl_18681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2178 v h) (hints_cons _ _ _ (der_18681 v h) (by intro d hd; cases hd)))
def cl_22611 : CNF.NClause := [(121,true),(50,false),(59,false),(53,false),(39,false),(42,false)]
theorem der_22611 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22611 :=
  CNF.rup_sound cl_22611 [cl_3778,cl_22607] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3778 v h) (hints_cons _ _ _ (der_22607 v h) (by intro d hd; cases hd)))
def cl_22612 : CNF.NClause := [(99,true),(60,false),(39,false),(35,true),(51,false),(47,false)]
theorem der_22612 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22612 :=
  CNF.rup_sound cl_22612 [cl_2374,cl_14913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2374 v h) (hints_cons _ _ _ (der_14913 v h) (by intro d hd; cases hd)))
def cl_22613 : CNF.NClause := [(110,true),(45,false),(46,false),(57,false),(52,false),(39,false)]
theorem der_22613 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22613 :=
  CNF.rup_sound cl_22613 [cl_3073,cl_3074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3073 v h) (hints_cons _ _ _ (inp_3074 v h) (by intro d hd; cases hd)))
def cl_22614 : CNF.NClause := [(99,true),(60,false),(39,false),(35,false),(47,false),(51,false)]
theorem der_22614 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22614 :=
  CNF.rup_sound cl_22614 [cl_2373,cl_14913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2373 v h) (hints_cons _ _ _ (der_14913 v h) (by intro d hd; cases hd)))
def cl_22615 : CNF.NClause := [(107,true),(58,false),(32,false),(39,false),(48,false),(55,false)]
theorem der_22615 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22615 :=
  CNF.rup_sound cl_22615 [cl_2881,cl_2885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2881 v h) (hints_cons _ _ _ (inp_2885 v h) (by intro d hd; cases hd)))
def cl_22616 : CNF.NClause := [(110,true),(45,false),(52,false),(57,false),(39,false),(33,true)]
theorem der_22616 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22616 :=
  CNF.rup_sound cl_22616 [cl_3082,cl_3074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3082 v h) (hints_cons _ _ _ (inp_3074 v h) (by intro d hd; cases hd)))
def cl_22617 : CNF.NClause := [(110,true),(33,true),(39,false),(46,true),(57,false),(45,false)]
theorem der_22617 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22617 :=
  CNF.rup_sound cl_22617 [cl_3098,cl_22616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3098 v h) (hints_cons _ _ _ (der_22616 v h) (by intro d hd; cases hd)))
def cl_22618 : CNF.NClause := [(110,true),(45,false),(46,true),(39,false),(52,false),(33,true)]
theorem der_22618 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22618 :=
  CNF.rup_sound cl_22618 [cl_3114,cl_22616] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3114 v h) (hints_cons _ _ _ (der_22616 v h) (by intro d hd; cases hd)))
def cl_22619 : CNF.NClause := [(110,true),(52,true),(39,false),(46,true),(57,true),(45,false)]
theorem der_22619 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22619 :=
  CNF.rup_sound cl_22619 [cl_3130,cl_21997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3130 v h) (hints_cons _ _ _ (der_21997 v h) (by intro d hd; cases hd)))
def cl_22620 : CNF.NClause := [(117,false),(32,true),(36,true),(49,true),(53,true),(45,true)]
theorem der_22620 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22620 :=
  CNF.rup_sound cl_22620 [cl_3584,cl_3552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3584 v h) (hints_cons _ _ _ (inp_3552 v h) (by intro d hd; cases hd)))
def cl_22621 : CNF.NClause := [(115,false),(55,true),(47,true),(44,true),(36,true),(33,true)]
theorem der_22621 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22621 :=
  CNF.rup_sound cl_22621 [cl_3456,cl_3424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3456 v h) (hints_cons _ _ _ (inp_3424 v h) (by intro d hd; cases hd)))
def cl_22622 : CNF.NClause := [(114,true),(42,false),(35,true),(36,true),(54,false),(48,false)]
theorem der_22622 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22622 :=
  CNF.rup_sound cl_22622 [cl_3332,cl_20320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3332 v h) (hints_cons _ _ _ (der_20320 v h) (by intro d hd; cases hd)))
def cl_22623 : CNF.NClause := [(114,true),(36,true),(48,false),(54,false),(57,false),(35,true)]
theorem der_22623 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22623 :=
  CNF.rup_sound cl_22623 [cl_3336,cl_22622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3336 v h) (hints_cons _ _ _ (der_22622 v h) (by intro d hd; cases hd)))
def cl_22624 : CNF.NClause := [(114,true),(42,false),(35,true),(54,false),(36,true),(48,true)]
theorem der_22624 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22624 :=
  CNF.rup_sound cl_22624 [cl_3340,cl_20320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3340 v h) (hints_cons _ _ _ (der_20320 v h) (by intro d hd; cases hd)))
def cl_22625 : CNF.NClause := [(114,true),(42,true),(36,true),(54,false),(57,false),(35,true)]
theorem der_22625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22625 :=
  CNF.rup_sound cl_22625 [cl_3344,cl_22623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3344 v h) (hints_cons _ _ _ (der_22623 v h) (by intro d hd; cases hd)))
def cl_22626 : CNF.NClause := [(114,true),(42,false),(36,true),(35,true),(48,false),(57,false)]
theorem der_22626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22626 :=
  CNF.rup_sound cl_22626 [cl_3348,cl_22622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3348 v h) (hints_cons _ _ _ (der_22622 v h) (by intro d hd; cases hd)))
def cl_22627 : CNF.NClause := [(114,true),(42,true),(36,true),(48,false),(35,true),(57,false)]
theorem der_22627 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22627 :=
  CNF.rup_sound cl_22627 [cl_3352,cl_22623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3352 v h) (hints_cons _ _ _ (der_22623 v h) (by intro d hd; cases hd)))
def cl_22628 : CNF.NClause := [(114,true),(48,true),(57,false),(35,true),(42,false),(36,true)]
theorem der_22628 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22628 :=
  CNF.rup_sound cl_22628 [cl_3356,cl_22624] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3356 v h) (hints_cons _ _ _ (der_22624 v h) (by intro d hd; cases hd)))
def cl_22629 : CNF.NClause := [(114,true),(57,true),(54,false),(35,true),(36,true),(48,false)]
theorem der_22629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22629 :=
  CNF.rup_sound cl_22629 [cl_3368,cl_20320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3368 v h) (hints_cons _ _ _ (der_20320 v h) (by intro d hd; cases hd)))
def cl_22630 : CNF.NClause := [(114,true),(35,true),(36,true),(57,true),(48,false),(42,false)]
theorem der_22630 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22630 :=
  CNF.rup_sound cl_22630 [cl_3380,cl_20320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3380 v h) (hints_cons _ _ _ (der_20320 v h) (by intro d hd; cases hd)))
def cl_22631 : CNF.NClause := [(114,false),(42,true),(48,true),(57,true),(36,true),(54,true)]
theorem der_22631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22631 :=
  CNF.rup_sound cl_22631 [cl_3392,cl_3391] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3392 v h) (hints_cons _ _ _ (inp_3391 v h) (by intro d hd; cases hd)))
def cl_22632 : CNF.NClause := [(116,false),(52,true),(36,true),(58,true),(50,true),(43,true)]
theorem der_22632 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22632 :=
  CNF.rup_sound cl_22632 [cl_3520,cl_3519] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3520 v h) (hints_cons _ _ _ (inp_3519 v h) (by intro d hd; cases hd)))
def cl_22633 : CNF.NClause := [(116,false),(36,true),(34,true),(52,true),(50,true),(43,true)]
theorem der_22633 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22633 :=
  CNF.rup_sound cl_22633 [cl_3488,cl_22632] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3488 v h) (hints_cons _ _ _ (der_22632 v h) (by intro d hd; cases hd)))
def cl_22634 : CNF.NClause := [(113,true),(37,false),(36,true),(39,false),(40,true),(61,true)]
theorem der_22634 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22634 :=
  CNF.rup_sound cl_22634 [cl_3318,cl_22608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3318 v h) (hints_cons _ _ _ (der_22608 v h) (by intro d hd; cases hd)))
def cl_22635 : CNF.NClause := [(113,true),(37,false),(36,true),(39,false),(40,false),(61,true)]
theorem der_22635 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22635 :=
  CNF.rup_sound cl_22635 [cl_3302,cl_22608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3302 v h) (hints_cons _ _ _ (der_22608 v h) (by intro d hd; cases hd)))
def cl_22636 : CNF.NClause := [(113,true),(37,false),(36,true),(38,true),(40,false),(61,true)]
theorem der_22636 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22636 :=
  CNF.rup_sound cl_22636 [cl_3310,cl_22635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3310 v h) (hints_cons _ _ _ (der_22635 v h) (by intro d hd; cases hd)))
def cl_22637 : CNF.NClause := [(113,true),(61,false),(37,false),(38,true),(40,true),(39,false)]
theorem der_22637 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22637 :=
  CNF.rup_sound cl_22637 [cl_3286,cl_21929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3286 v h) (hints_cons _ _ _ (der_21929 v h) (by intro d hd; cases hd)))
def cl_22638 : CNF.NClause := [(61,false),(113,true),(38,true),(37,false),(40,true),(36,true)]
theorem der_22638 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22638 :=
  CNF.rup_sound cl_22638 [cl_3294,cl_22637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3294 v h) (hints_cons _ _ _ (der_22637 v h) (by intro d hd; cases hd)))
def cl_22639 : CNF.NClause := [(114,true),(36,true),(48,false),(42,true),(54,false),(57,false)]
theorem der_22639 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22639 :=
  CNF.rup_sound cl_22639 [cl_3335,cl_22623] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3335 v h) (hints_cons _ _ _ (der_22623 v h) (by intro d hd; cases hd)))
def cl_22640 : CNF.NClause := [(117,false),(32,true),(49,true),(53,true),(36,true),(60,true)]
theorem der_22640 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22640 :=
  CNF.rup_sound cl_22640 [cl_3580,cl_22620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3580 v h) (hints_cons _ _ _ (der_22620 v h) (by intro d hd; cases hd)))
def cl_22641 : CNF.NClause := [(116,true),(50,false),(52,false),(43,false),(36,true),(34,true)]
theorem der_22641 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22641 :=
  CNF.rup_sound cl_22641 [cl_3492,cl_15173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3492 v h) (hints_cons _ _ _ (der_15173 v h) (by intro d hd; cases hd)))
def cl_22642 : CNF.NClause := [(123,true),(51,true),(36,true),(31,true),(46,false),(56,false)]
theorem der_22642 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22642 :=
  CNF.rup_sound cl_22642 [cl_3924,cl_22028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3924 v h) (hints_cons _ _ _ (der_22028 v h) (by intro d hd; cases hd)))
def cl_22643 : CNF.NClause := [(123,true),(51,true),(36,true),(46,false),(31,false),(56,false)]
theorem der_22643 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22643 :=
  CNF.rup_sound cl_22643 [cl_3923,cl_20314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3923 v h) (hints_cons _ _ _ (der_20314 v h) (by intro d hd; cases hd)))
def cl_22644 : CNF.NClause := [(113,true),(37,false),(38,false),(61,false),(39,true),(40,true)]
theorem der_22644 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22644 :=
  CNF.rup_sound cl_22644 [cl_3290,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3290 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_22645 : CNF.NClause := [(123,true),(56,false),(31,false),(46,false),(51,false),(36,true)]
theorem der_22645 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22645 :=
  CNF.rup_sound cl_22645 [cl_3907,cl_20314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3907 v h) (hints_cons _ _ _ (der_20314 v h) (by intro d hd; cases hd)))
def cl_22646 : CNF.NClause := [(114,true),(36,true),(42,false),(57,false),(54,false),(48,false)]
theorem der_22646 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22646 :=
  CNF.rup_sound cl_22646 [cl_3331,cl_22622] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3331 v h) (hints_cons _ _ _ (der_22622 v h) (by intro d hd; cases hd)))
def cl_22647 : CNF.NClause := [(115,true),(44,false),(33,false),(59,false),(55,false),(36,true)]
theorem der_22647 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22647 :=
  CNF.rup_sound cl_22647 [cl_3395,cl_18218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3395 v h) (hints_cons _ _ _ (der_18218 v h) (by intro d hd; cases hd)))
def cl_22648 : CNF.NClause := [(117,true),(60,false),(36,true),(32,false),(49,false),(45,false)]
theorem der_22648 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22648 :=
  CNF.rup_sound cl_22648 [cl_3523,cl_18288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3523 v h) (hints_cons _ _ _ (der_18288 v h) (by intro d hd; cases hd)))
def cl_22649 : CNF.NClause := [(113,true),(37,false),(39,true),(40,false),(38,false),(61,false)]
theorem der_22649 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22649 :=
  CNF.rup_sound cl_22649 [cl_3274,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3274 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_22650 : CNF.NClause := [(113,true),(37,false),(39,false),(36,true),(38,false),(40,false)]
theorem der_22650 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22650 :=
  CNF.rup_sound cl_22650 [cl_3266,cl_22608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3266 v h) (hints_cons _ _ _ (der_22608 v h) (by intro d hd; cases hd)))
def cl_22651 : CNF.NClause := [(113,true),(61,false),(37,true),(39,false),(38,false),(40,false)]
theorem der_22651 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22651 :=
  CNF.rup_sound cl_22651 [cl_3268,cl_21930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3268 v h) (hints_cons _ _ _ (der_21930 v h) (by intro d hd; cases hd)))
def cl_22652 : CNF.NClause := [(116,true),(58,false),(34,false),(50,false),(36,true),(52,false)]
theorem der_22652 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22652 :=
  CNF.rup_sound cl_22652 [cl_3463,cl_15173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3463 v h) (hints_cons _ _ _ (der_15173 v h) (by intro d hd; cases hd)))
def cl_22653 : CNF.NClause := [(116,true),(58,false),(43,true),(36,true),(52,false),(34,false)]
theorem der_22653 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22653 :=
  CNF.rup_sound cl_22653 [cl_3471,cl_22652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3471 v h) (hints_cons _ _ _ (der_22652 v h) (by intro d hd; cases hd)))
def cl_22654 : CNF.NClause := [(116,true),(58,false),(34,false),(50,false),(52,true),(43,true)]
theorem der_22654 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22654 :=
  CNF.rup_sound cl_22654 [cl_3479,cl_3477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3479 v h) (hints_cons _ _ _ (inp_3477 v h) (by intro d hd; cases hd)))
def cl_22655 : CNF.NClause := [(116,true),(58,false),(43,true),(36,true),(52,true),(34,false)]
theorem der_22655 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22655 :=
  CNF.rup_sound cl_22655 [cl_3487,cl_22654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3487 v h) (hints_cons _ _ _ (der_22654 v h) (by intro d hd; cases hd)))
def cl_22656 : CNF.NClause := [(116,true),(50,false),(34,false),(52,false),(36,true),(43,true)]
theorem der_22656 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22656 :=
  CNF.rup_sound cl_22656 [cl_3495,cl_22652] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3495 v h) (hints_cons _ _ _ (der_22652 v h) (by intro d hd; cases hd)))
def cl_22657 : CNF.NClause := [(116,true),(58,true),(34,false),(36,true),(52,false),(43,true)]
theorem der_22657 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22657 :=
  CNF.rup_sound cl_22657 [cl_3503,cl_22656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3503 v h) (hints_cons _ _ _ (der_22656 v h) (by intro d hd; cases hd)))
def cl_22658 : CNF.NClause := [(116,true),(50,false),(34,false),(43,true),(52,true),(58,true)]
theorem der_22658 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22658 :=
  CNF.rup_sound cl_22658 [cl_3511,cl_22529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3511 v h) (hints_cons _ _ _ (der_22529 v h) (by intro d hd; cases hd)))
def cl_22659 : CNF.NClause := [(116,true),(50,false),(34,true),(58,false),(52,false),(36,true)]
theorem der_22659 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22659 :=
  CNF.rup_sound cl_22659 [cl_3464,cl_15173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3464 v h) (hints_cons _ _ _ (der_15173 v h) (by intro d hd; cases hd)))
def cl_22660 : CNF.NClause := [(123,true),(31,true),(51,false),(36,true),(56,false),(46,false)]
theorem der_22660 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22660 :=
  CNF.rup_sound cl_22660 [cl_3908,cl_19240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3908 v h) (hints_cons _ _ _ (der_19240 v h) (by intro d hd; cases hd)))
def cl_22661 : CNF.NClause := [(117,true),(60,false),(36,true),(49,false),(45,false),(32,true)]
theorem der_22661 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22661 :=
  CNF.rup_sound cl_22661 [cl_3524,cl_21926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3524 v h) (hints_cons _ _ _ (der_21926 v h) (by intro d hd; cases hd)))
def cl_22662 : CNF.NClause := [(117,true),(60,false),(36,true),(32,true),(49,false),(45,true)]
theorem der_22662 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22662 :=
  CNF.rup_sound cl_22662 [cl_3528,cl_21926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3528 v h) (hints_cons _ _ _ (der_21926 v h) (by intro d hd; cases hd)))
def cl_22663 : CNF.NClause := [(117,true),(60,false),(36,true),(45,false),(32,true),(53,false)]
theorem der_22663 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22663 :=
  CNF.rup_sound cl_22663 [cl_3532,cl_22661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3532 v h) (hints_cons _ _ _ (der_22661 v h) (by intro d hd; cases hd)))
def cl_22664 : CNF.NClause := [(117,true),(60,false),(36,true),(32,true),(53,false),(49,true)]
theorem der_22664 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22664 :=
  CNF.rup_sound cl_22664 [cl_3536,cl_22663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3536 v h) (hints_cons _ _ _ (der_22663 v h) (by intro d hd; cases hd)))
def cl_22665 : CNF.NClause := [(117,true),(60,false),(32,true),(36,true),(53,true),(45,false)]
theorem der_22665 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22665 :=
  CNF.rup_sound cl_22665 [cl_3548,cl_21926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3548 v h) (hints_cons _ _ _ (der_21926 v h) (by intro d hd; cases hd)))
def cl_22666 : CNF.NClause := [(117,true),(49,false),(36,true),(53,false),(32,true),(45,false)]
theorem der_22666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22666 :=
  CNF.rup_sound cl_22666 [cl_3556,cl_22661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3556 v h) (hints_cons _ _ _ (der_22661 v h) (by intro d hd; cases hd)))
def cl_22667 : CNF.NClause := [(117,true),(49,false),(36,true),(60,true),(32,true),(53,false)]
theorem der_22667 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22667 :=
  CNF.rup_sound cl_22667 [cl_3560,cl_22666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3560 v h) (hints_cons _ _ _ (der_22666 v h) (by intro d hd; cases hd)))
def cl_22668 : CNF.NClause := [(117,true),(45,false),(36,true),(32,true),(53,false),(60,true)]
theorem der_22668 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22668 :=
  CNF.rup_sound cl_22668 [cl_3564,cl_22666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3564 v h) (hints_cons _ _ _ (der_22666 v h) (by intro d hd; cases hd)))
def cl_22669 : CNF.NClause := [(117,true),(49,false),(60,true),(36,true),(45,false),(53,true)]
theorem der_22669 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22669 :=
  CNF.rup_sound cl_22669 [cl_3572,cl_18288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3572 v h) (hints_cons _ _ _ (der_18288 v h) (by intro d hd; cases hd)))
def cl_22670 : CNF.NClause := [(123,true),(46,true),(36,true),(31,false),(51,false),(56,false)]
theorem der_22670 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22670 :=
  CNF.rup_sound cl_22670 [cl_3915,cl_19993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3915 v h) (hints_cons _ _ _ (der_19993 v h) (by intro d hd; cases hd)))
def cl_22671 : CNF.NClause := [(120,true),(31,false),(45,true),(38,true),(54,false),(58,false)]
theorem der_22671 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22671 :=
  CNF.rup_sound cl_22671 [cl_3719,cl_20001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3719 v h) (hints_cons _ _ _ (der_20001 v h) (by intro d hd; cases hd)))
def cl_22672 : CNF.NClause := [(120,true),(31,false),(45,true),(38,true),(47,false),(58,false)]
theorem der_22672 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22672 :=
  CNF.rup_sound cl_22672 [cl_3735,cl_22671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3735 v h) (hints_cons _ _ _ (der_22671 v h) (by intro d hd; cases hd)))
def cl_22673 : CNF.NClause := [(120,true),(31,false),(45,true),(38,true),(58,false),(47,true)]
theorem der_22673 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22673 :=
  CNF.rup_sound cl_22673 [cl_3743,cl_20001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3743 v h) (hints_cons _ _ _ (der_20001 v h) (by intro d hd; cases hd)))
def cl_22674 : CNF.NClause := [(45,true),(31,false),(120,true),(38,true),(58,true),(54,false)]
theorem der_22674 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22674 :=
  CNF.rup_sound cl_22674 [cl_3751,cl_20001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3751 v h) (hints_cons _ _ _ (der_20001 v h) (by intro d hd; cases hd)))
def cl_22675 : CNF.NClause := [(120,true),(31,false),(47,false),(38,true),(45,true),(54,true)]
theorem der_22675 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22675 :=
  CNF.rup_sound cl_22675 [cl_3767,cl_22672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3767 v h) (hints_cons _ _ _ (der_22672 v h) (by intro d hd; cases hd)))
def cl_22676 : CNF.NClause := [(37,false),(36,false),(40,true),(38,true),(39,false),(113,true)]
theorem der_22676 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22676 :=
  CNF.rup_sound cl_22676 [cl_3317,cl_21929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3317 v h) (hints_cons _ _ _ (der_21929 v h) (by intro d hd; cases hd)))
def cl_22677 : CNF.NClause := [(113,true),(61,false),(37,true),(39,false),(38,true),(40,true)]
theorem der_22677 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22677 :=
  CNF.rup_sound cl_22677 [cl_3288,cl_21930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3288 v h) (hints_cons _ _ _ (der_21930 v h) (by intro d hd; cases hd)))
def cl_22678 : CNF.NClause := [(113,true),(38,true),(61,true),(40,false),(39,false),(36,true)]
theorem der_22678 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22678 :=
  CNF.rup_sound cl_22678 [cl_3304,cl_22636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3304 v h) (hints_cons _ _ _ (der_22636 v h) (by intro d hd; cases hd)))
def cl_22679 : CNF.NClause := [(104,true),(49,false),(41,true),(59,false),(38,true),(35,false)]
theorem der_22679 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22679 :=
  CNF.rup_sound cl_22679 [cl_2695,cl_18364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2695 v h) (hints_cons _ _ _ (der_18364 v h) (by intro d hd; cases hd)))
def cl_22680 : CNF.NClause := [(113,true),(36,true),(39,false),(37,false),(40,false),(38,true)]
theorem der_22680 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22680 :=
  CNF.rup_sound cl_22680 [cl_3270,cl_22635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3270 v h) (hints_cons _ _ _ (der_22635 v h) (by intro d hd; cases hd)))
def cl_22681 : CNF.NClause := [(120,true),(58,false),(38,true),(31,false),(47,false),(54,true)]
theorem der_22681 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22681 :=
  CNF.rup_sound cl_22681 [cl_3731,cl_22672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3731 v h) (hints_cons _ _ _ (der_22672 v h) (by intro d hd; cases hd)))
def cl_22682 : CNF.NClause := [(120,true),(31,false),(54,true),(38,true),(47,false),(58,true)]
theorem der_22682 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22682 :=
  CNF.rup_sound cl_22682 [cl_3763,cl_22675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3763 v h) (hints_cons _ _ _ (der_22675 v h) (by intro d hd; cases hd)))
def cl_22683 : CNF.NClause := [(113,true),(61,false),(38,true),(39,true),(40,false),(37,false)]
theorem der_22683 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22683 :=
  CNF.rup_sound cl_22683 [cl_3278,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3278 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_22684 : CNF.NClause := [(111,true),(60,false),(38,true),(42,true),(46,false),(55,false)]
theorem der_22684 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22684 :=
  CNF.rup_sound cl_22684 [cl_3143,cl_21927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3143 v h) (hints_cons _ _ _ (der_21927 v h) (by intro d hd; cases hd)))
def cl_22685 : CNF.NClause := [(111,true),(60,false),(38,true),(42,true),(55,false),(34,false)]
theorem der_22685 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22685 :=
  CNF.rup_sound cl_22685 [cl_3151,cl_22684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3151 v h) (hints_cons _ _ _ (der_22684 v h) (by intro d hd; cases hd)))
def cl_22686 : CNF.NClause := [(111,true),(60,false),(38,true),(42,true),(46,false),(34,false)]
theorem der_22686 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22686 :=
  CNF.rup_sound cl_22686 [cl_3159,cl_22684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3159 v h) (hints_cons _ _ _ (der_22684 v h) (by intro d hd; cases hd)))
def cl_22687 : CNF.NClause := [(111,true),(60,false),(38,true),(42,true),(46,true),(34,false)]
theorem der_22687 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22687 :=
  CNF.rup_sound cl_22687 [cl_3167,cl_22685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3167 v h) (hints_cons _ _ _ (der_22685 v h) (by intro d hd; cases hd)))
def cl_22688 : CNF.NClause := [(111,true),(38,true),(42,true),(46,false),(55,false),(60,true)]
theorem der_22688 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22688 :=
  CNF.rup_sound cl_22688 [cl_3175,cl_21927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3175 v h) (hints_cons _ _ _ (der_21927 v h) (by intro d hd; cases hd)))
def cl_22689 : CNF.NClause := [(111,true),(38,true),(46,true),(42,true),(55,false),(34,false)]
theorem der_22689 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22689 :=
  CNF.rup_sound cl_22689 [cl_3183,cl_22685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3183 v h) (hints_cons _ _ _ (der_22685 v h) (by intro d hd; cases hd)))
def cl_22690 : CNF.NClause := [(111,true),(38,true),(42,true),(34,false),(46,false),(55,true)]
theorem der_22690 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22690 :=
  CNF.rup_sound cl_22690 [cl_3191,cl_22686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3191 v h) (hints_cons _ _ _ (der_22686 v h) (by intro d hd; cases hd)))
def cl_22691 : CNF.NClause := [(120,true),(31,false),(58,true),(45,false),(38,true),(54,false)]
theorem der_22691 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22691 :=
  CNF.rup_sound cl_22691 [cl_3747,cl_20001] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3747 v h) (hints_cons _ _ _ (der_20001 v h) (by intro d hd; cases hd)))
def cl_22692 : CNF.NClause := [(102,true),(44,false),(51,true),(38,true),(32,false),(50,false)]
theorem der_22692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22692 :=
  CNF.rup_sound cl_22692 [cl_2579,cl_21989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2579 v h) (hints_cons _ _ _ (der_21989 v h) (by intro d hd; cases hd)))
def cl_22693 : CNF.NClause := [(104,true),(35,false),(59,true),(49,false),(38,true),(41,true)]
theorem der_22693 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22693 :=
  CNF.rup_sound cl_22693 [cl_2727,cl_19315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2727 v h) (hints_cons _ _ _ (der_19315 v h) (by intro d hd; cases hd)))
def cl_22694 : CNF.NClause := [(95,true),(38,true),(33,false),(53,false),(48,false),(56,false)]
theorem der_22694 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22694 :=
  CNF.rup_sound cl_22694 [cl_2119,cl_15167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2119 v h) (hints_cons _ _ _ (der_15167 v h) (by intro d hd; cases hd)))
def cl_22695 : CNF.NClause := [(95,true),(38,true),(33,false),(56,false),(53,false),(48,true)]
theorem der_22695 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22695 :=
  CNF.rup_sound cl_22695 [cl_2127,cl_21978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2127 v h) (hints_cons _ _ _ (der_21978 v h) (by intro d hd; cases hd)))
def cl_22696 : CNF.NClause := [(95,true),(56,false),(48,true),(53,true),(33,false),(43,true)]
theorem der_22696 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22696 :=
  CNF.rup_sound cl_22696 [cl_2143,cl_22525] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2143 v h) (hints_cons _ _ _ (der_22525 v h) (by intro d hd; cases hd)))
def cl_22697 : CNF.NClause := [(95,true),(38,true),(33,false),(43,true),(53,false),(48,false)]
theorem der_22697 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22697 :=
  CNF.rup_sound cl_22697 [cl_2151,cl_22694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2151 v h) (hints_cons _ _ _ (der_22694 v h) (by intro d hd; cases hd)))
def cl_22698 : CNF.NClause := [(95,true),(33,false),(43,true),(38,true),(53,false),(48,true)]
theorem der_22698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22698 :=
  CNF.rup_sound cl_22698 [cl_2159,cl_22695] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2159 v h) (hints_cons _ _ _ (der_22695 v h) (by intro d hd; cases hd)))
def cl_22699 : CNF.NClause := [(95,true),(33,false),(43,true),(48,false),(38,true),(53,true)]
theorem der_22699 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22699 :=
  CNF.rup_sound cl_22699 [cl_2167,cl_19135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2167 v h) (hints_cons _ _ _ (der_19135 v h) (by intro d hd; cases hd)))
def cl_22700 : CNF.NClause := [(102,true),(44,false),(38,true),(50,false),(32,false),(51,false)]
theorem der_22700 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22700 :=
  CNF.rup_sound cl_22700 [cl_2563,cl_20352] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2563 v h) (hints_cons _ _ _ (der_20352 v h) (by intro d hd; cases hd)))
def cl_22701 : CNF.NClause := [(104,true),(38,true),(52,false),(49,false),(35,false),(59,false)]
theorem der_22701 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22701 :=
  CNF.rup_sound cl_22701 [cl_2691,cl_22679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2691 v h) (hints_cons _ _ _ (der_22679 v h) (by intro d hd; cases hd)))
def cl_22702 : CNF.NClause := [(95,true),(53,false),(38,true),(48,false),(33,true),(56,false)]
theorem der_22702 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22702 :=
  CNF.rup_sound cl_22702 [cl_2120,cl_15167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2120 v h) (hints_cons _ _ _ (der_15167 v h) (by intro d hd; cases hd)))
def cl_22703 : CNF.NClause := [(102,true),(44,false),(57,false),(38,true),(50,false),(51,false)]
theorem der_22703 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22703 :=
  CNF.rup_sound cl_22703 [cl_2564,cl_22700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2564 v h) (hints_cons _ _ _ (der_22700 v h) (by intro d hd; cases hd)))
def cl_22704 : CNF.NClause := [(104,true),(41,false),(38,true),(49,false),(52,false),(59,false)]
theorem der_22704 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22704 :=
  CNF.rup_sound cl_22704 [cl_2692,cl_22701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2692 v h) (hints_cons _ _ _ (der_22701 v h) (by intro d hd; cases hd)))
def cl_22705 : CNF.NClause := [(104,true),(49,false),(59,false),(41,true),(38,true),(35,true)]
theorem der_22705 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22705 :=
  CNF.rup_sound cl_22705 [cl_2696,cl_18364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2696 v h) (hints_cons _ _ _ (der_18364 v h) (by intro d hd; cases hd)))
def cl_22706 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(52,false),(59,false)]
theorem der_22706 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22706 :=
  CNF.rup_sound cl_22706 [cl_2700,cl_22704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2700 v h) (hints_cons _ _ _ (der_22704 v h) (by intro d hd; cases hd)))
def cl_22707 : CNF.NClause := [(104,true),(38,true),(41,true),(35,true),(52,false),(59,false)]
theorem der_22707 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22707 :=
  CNF.rup_sound cl_22707 [cl_2704,cl_22705] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2704 v h) (hints_cons _ _ _ (der_22705 v h) (by intro d hd; cases hd)))
def cl_22708 : CNF.NClause := [(104,true),(38,true),(35,true),(49,false),(52,true),(59,false)]
theorem der_22708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22708 :=
  CNF.rup_sound cl_22708 [cl_2708,cl_18364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2708 v h) (hints_cons _ _ _ (der_18364 v h) (by intro d hd; cases hd)))
def cl_22709 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(52,true),(59,false)]
theorem der_22709 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22709 :=
  CNF.rup_sound cl_22709 [cl_2716,cl_22708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2716 v h) (hints_cons _ _ _ (der_22708 v h) (by intro d hd; cases hd)))
def cl_22710 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(49,false),(52,false)]
theorem der_22710 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22710 :=
  CNF.rup_sound cl_22710 [cl_2724,cl_22704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2724 v h) (hints_cons _ _ _ (der_22704 v h) (by intro d hd; cases hd)))
def cl_22711 : CNF.NClause := [(104,true),(49,false),(38,true),(41,true),(59,true),(52,false)]
theorem der_22711 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22711 :=
  CNF.rup_sound cl_22711 [cl_2728,cl_22693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2728 v h) (hints_cons _ _ _ (der_22693 v h) (by intro d hd; cases hd)))
def cl_22712 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(52,false),(59,true)]
theorem der_22712 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22712 :=
  CNF.rup_sound cl_22712 [cl_2732,cl_22710] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2732 v h) (hints_cons _ _ _ (der_22710 v h) (by intro d hd; cases hd)))
def cl_22713 : CNF.NClause := [(104,true),(41,false),(38,true),(35,true),(49,false),(52,true)]
theorem der_22713 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22713 :=
  CNF.rup_sound cl_22713 [cl_2740,cl_22708] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2740 v h) (hints_cons _ _ _ (der_22708 v h) (by intro d hd; cases hd)))
def cl_22714 : CNF.NClause := [(61,false),(82,true),(30,true),(77,false),(67,false),(87,false)]
theorem der_22714 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22714 :=
  CNF.rup_sound cl_22714 [cl_20062,cl_17875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_20062 v h) (hints_cons _ _ _ (der_17875 v h) (by intro d hd; cases hd)))
def cl_22715 : CNF.NClause := [(61,false),(82,true),(30,true),(72,false),(87,false),(67,false)]
theorem der_22715 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22715 :=
  CNF.rup_sound cl_22715 [cl_19155,cl_17875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_19155 v h) (hints_cons _ _ _ (der_17875 v h) (by intro d hd; cases hd)))
def cl_22716 : CNF.NClause := [(103,true),(61,false),(41,false),(43,false),(42,false),(44,false)]
theorem der_22716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22716 :=
  CNF.rup_sound cl_22716 [cl_2641,cl_21991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2641 v h) (hints_cons _ _ _ (der_21991 v h) (by intro d hd; cases hd)))
def cl_22717 : CNF.NClause := [(103,true),(41,false),(61,false),(44,false),(45,false),(43,true)]
theorem der_22717 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22717 :=
  CNF.rup_sound cl_22717 [cl_2629,cl_21931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2629 v h) (hints_cons _ _ _ (der_21931 v h) (by intro d hd; cases hd)))
def cl_22718 : CNF.NClause := [(108,true),(61,false),(47,false),(48,false),(49,false),(50,false)]
theorem der_22718 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22718 :=
  CNF.rup_sound cl_22718 [cl_2946,cl_2945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2946 v h) (hints_cons _ _ _ (inp_2945 v h) (by intro d hd; cases hd)))
def cl_22719 : CNF.NClause := [(103,true),(61,false),(41,true),(43,true),(44,false),(45,false)]
theorem der_22719 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22719 :=
  CNF.rup_sound cl_22719 [cl_2630,cl_21931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2630 v h) (hints_cons _ _ _ (der_21931 v h) (by intro d hd; cases hd)))
def cl_22720 : CNF.NClause := [(100,true),(49,false),(33,false),(42,true),(51,true),(58,true)]
theorem der_22720 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22720 :=
  CNF.rup_sound cl_22720 [cl_2485,cl_22012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2485 v h) (hints_cons _ _ _ (der_22012 v h) (by intro d hd; cases hd)))
def cl_22721 : CNF.NClause := [(100,true),(49,false),(33,false),(40,false),(51,true),(58,false)]
theorem der_22721 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22721 :=
  CNF.rup_sound cl_22721 [cl_2449,cl_2453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2449 v h) (hints_cons _ _ _ (inp_2453 v h) (by intro d hd; cases hd)))
def cl_22722 : CNF.NClause := [(100,true),(49,false),(33,false),(42,false),(51,true),(58,true)]
theorem der_22722 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22722 :=
  CNF.rup_sound cl_22722 [cl_2481,cl_18879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2481 v h) (hints_cons _ _ _ (der_18879 v h) (by intro d hd; cases hd)))
def cl_22723 : CNF.NClause := [(112,true),(43,false),(46,false),(59,true),(32,true),(54,false)]
theorem der_22723 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22723 :=
  CNF.rup_sound cl_22723 [cl_3234,cl_20324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3234 v h) (hints_cons _ _ _ (der_20324 v h) (by intro d hd; cases hd)))
def cl_22724 : CNF.NClause := [(106,true),(41,false),(34,true),(47,true),(40,false),(57,false)]
theorem der_22724 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22724 :=
  CNF.rup_sound cl_22724 [cl_2842,cl_2826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2842 v h) (hints_cons _ _ _ (inp_2826 v h) (by intro d hd; cases hd)))
def cl_22725 : CNF.NClause := [(106,true),(41,false),(34,true),(47,true),(40,false),(53,false)]
theorem der_22725 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22725 :=
  CNF.rup_sound cl_22725 [cl_2858,cl_2826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2858 v h) (hints_cons _ _ _ (inp_2826 v h) (by intro d hd; cases hd)))
def cl_22726 : CNF.NClause := [(106,true),(41,false),(34,true),(47,true),(40,false),(53,true)]
theorem der_22726 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22726 :=
  CNF.rup_sound cl_22726 [cl_2874,cl_22724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2874 v h) (hints_cons _ _ _ (der_22724 v h) (by intro d hd; cases hd)))
def cl_22727 : CNF.NClause := [(106,true),(53,false),(57,false),(41,true),(34,false),(40,false)]
theorem der_22727 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22727 :=
  CNF.rup_sound cl_22727 [cl_2829,cl_15545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2829 v h) (hints_cons _ _ _ (der_15545 v h) (by intro d hd; cases hd)))
def cl_22728 : CNF.NClause := [(106,true),(47,true),(41,true),(34,false),(57,false),(40,false)]
theorem der_22728 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22728 :=
  CNF.rup_sound cl_22728 [cl_2845,cl_22727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2845 v h) (hints_cons _ _ _ (der_22727 v h) (by intro d hd; cases hd)))
def cl_22729 : CNF.NClause := [(106,true),(53,false),(40,false),(41,true),(34,false),(47,true)]
theorem der_22729 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22729 :=
  CNF.rup_sound cl_22729 [cl_2861,cl_22728] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2861 v h) (hints_cons _ _ _ (der_22728 v h) (by intro d hd; cases hd)))
def cl_22730 : CNF.NClause := [(106,true),(41,true),(40,false),(34,false),(47,true),(57,true)]
theorem der_22730 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22730 :=
  CNF.rup_sound cl_22730 [cl_2877,cl_22729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2877 v h) (hints_cons _ _ _ (der_22729 v h) (by intro d hd; cases hd)))
def cl_22731 : CNF.NClause := [(106,true),(53,false),(34,true),(40,false),(57,false),(47,true)]
theorem der_22731 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22731 :=
  CNF.rup_sound cl_22731 [cl_2830,cl_2826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2830 v h) (hints_cons _ _ _ (inp_2826 v h) (by intro d hd; cases hd)))
def cl_22732 : CNF.NClause := [(106,true),(47,true),(34,true),(57,false),(53,true),(40,false)]
theorem der_22732 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22732 :=
  CNF.rup_sound cl_22732 [cl_2846,cl_22724] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2846 v h) (hints_cons _ _ _ (der_22724 v h) (by intro d hd; cases hd)))
def cl_22733 : CNF.NClause := [(106,true),(53,false),(40,false),(41,true),(47,true),(57,true)]
theorem der_22733 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22733 :=
  CNF.rup_sound cl_22733 [cl_2862,cl_22729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2862 v h) (hints_cons _ _ _ (der_22729 v h) (by intro d hd; cases hd)))
def cl_22734 : CNF.NClause := [(94,true),(50,false),(56,false),(40,false),(55,false),(45,false)]
theorem der_22734 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22734 :=
  CNF.rup_sound cl_22734 [cl_2049,cl_2050] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2049 v h) (hints_cons _ _ _ (inp_2050 v h) (by intro d hd; cases hd)))
def cl_22735 : CNF.NClause := [(106,true),(41,false),(57,false),(47,false),(40,false),(53,false)]
theorem der_22735 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22735 :=
  CNF.rup_sound cl_22735 [cl_2818,cl_15545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2818 v h) (hints_cons _ _ _ (der_15545 v h) (by intro d hd; cases hd)))
def cl_22736 : CNF.NClause := [(119,true),(60,false),(48,false),(44,false),(52,false),(40,false)]
theorem der_22736 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22736 :=
  CNF.rup_sound cl_22736 [cl_3650,cl_3649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3650 v h) (hints_cons _ _ _ (inp_3649 v h) (by intro d hd; cases hd)))
def cl_22737 : CNF.NClause := [(113,true),(61,false),(36,false),(40,false),(39,true),(38,true)]
theorem der_22737 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22737 :=
  CNF.rup_sound cl_22737 [cl_3279,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3279 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_22738 : CNF.NClause := [(113,true),(36,false),(38,true),(39,true),(37,true),(40,false)]
theorem der_22738 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22738 :=
  CNF.rup_sound cl_22738 [cl_3311,cl_22737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3311 v h) (hints_cons _ _ _ (der_22737 v h) (by intro d hd; cases hd)))
def cl_22739 : CNF.NClause := [(113,true),(61,false),(36,false),(38,false),(39,true),(40,false)]
theorem der_22739 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22739 :=
  CNF.rup_sound cl_22739 [cl_3275,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3275 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_22740 : CNF.NClause := [(113,true),(36,false),(40,false),(61,true),(39,true),(37,true)]
theorem der_22740 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22740 :=
  CNF.rup_sound cl_22740 [cl_3307,cl_22738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3307 v h) (hints_cons _ _ _ (der_22738 v h) (by intro d hd; cases hd)))
def cl_22741 : CNF.NClause := [(113,true),(37,false),(40,false),(38,true),(36,false),(39,true)]
theorem der_22741 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22741 :=
  CNF.rup_sound cl_22741 [cl_3309,cl_15589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3309 v h) (hints_cons _ _ _ (der_15589 v h) (by intro d hd; cases hd)))
def cl_22742 : CNF.NClause := [(113,true),(61,false),(39,true),(40,false),(37,true),(38,true)]
theorem der_22742 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22742 :=
  CNF.rup_sound cl_22742 [cl_3280,cl_22737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3280 v h) (hints_cons _ _ _ (der_22737 v h) (by intro d hd; cases hd)))
def cl_22743 : CNF.NClause := [(32,false),(112,true),(46,true),(43,true),(54,false),(59,false)]
theorem der_22743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22743 :=
  CNF.rup_sound cl_22743 [cl_3213,cl_19153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3213 v h) (hints_cons _ _ _ (der_19153 v h) (by intro d hd; cases hd)))
def cl_22744 : CNF.NClause := [(32,false),(112,true),(40,false),(43,true),(54,false),(59,false)]
theorem der_22744 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22744 :=
  CNF.rup_sound cl_22744 [cl_3205,cl_22743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3205 v h) (hints_cons _ _ _ (der_22743 v h) (by intro d hd; cases hd)))
def cl_22745 : CNF.NClause := [(100,true),(58,false),(42,true),(40,false),(49,false),(33,false)]
theorem der_22745 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22745 :=
  CNF.rup_sound cl_22745 [cl_2437,cl_2453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2437 v h) (hints_cons _ _ _ (inp_2453 v h) (by intro d hd; cases hd)))
def cl_22746 : CNF.NClause := [(58,false),(42,false),(33,false),(40,false),(100,true),(49,false)]
theorem der_22746 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_22746 :=
  CNF.rup_sound cl_22746 [cl_2433,cl_22721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2433 v h) (hints_cons _ _ _ (der_22721 v h) (by intro d hd; cases hd)))
end P2000
end Percolation.Replay
