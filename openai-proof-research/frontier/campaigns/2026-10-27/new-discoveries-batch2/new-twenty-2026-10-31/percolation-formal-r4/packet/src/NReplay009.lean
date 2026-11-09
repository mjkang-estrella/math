import NReplay008
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_26787 : CNF.NClause := [(40,false),(9,true),(63,false),(75,true),(81,true),(82,false),(88,false)]
theorem der_26787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26787 :=
  CNF.rup_sound cl_26787 [cl_5150,cl_26786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5150 v h) (hints_cons _ _ _ (der_26786 v h) (by intro d hd; cases hd)))
def cl_26788 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,false),(81,false),(88,false)]
theorem der_26788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26788 :=
  CNF.rup_sound cl_26788 [cl_5158,cl_26781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5158 v h) (hints_cons _ _ _ (der_26781 v h) (by intro d hd; cases hd)))
def cl_26789 : CNF.NClause := [(40,false),(9,true),(69,false),(63,false),(81,false),(75,true),(88,false)]
theorem der_26789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26789 :=
  CNF.rup_sound cl_26789 [cl_5162,cl_26782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5162 v h) (hints_cons _ _ _ (der_26782 v h) (by intro d hd; cases hd)))
def cl_26790 : CNF.NClause := [(40,false),(9,true),(63,false),(75,true),(81,false),(82,true),(88,false)]
theorem der_26790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26790 :=
  CNF.rup_sound cl_26790 [cl_5166,cl_26789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5166 v h) (hints_cons _ _ _ (der_26789 v h) (by intro d hd; cases hd)))
def cl_26791 : CNF.NClause := [(40,false),(9,true),(69,false),(75,false),(63,false),(81,true),(88,false)]
theorem der_26791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26791 :=
  CNF.rup_sound cl_26791 [cl_5170,cl_26784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5170 v h) (hints_cons _ _ _ (der_26784 v h) (by intro d hd; cases hd)))
def cl_26792 : CNF.NClause := [(40,false),(9,true),(63,false),(75,false),(81,true),(82,true),(88,false)]
theorem der_26792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26792 :=
  CNF.rup_sound cl_26792 [cl_5174,cl_26791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5174 v h) (hints_cons _ _ _ (der_26791 v h) (by intro d hd; cases hd)))
def cl_26793 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(63,false),(82,true),(88,false)]
theorem der_26793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26793 :=
  CNF.rup_sound cl_26793 [cl_5178,cl_26792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5178 v h) (hints_cons _ _ _ (der_26792 v h) (by intro d hd; cases hd)))
def cl_26794 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,true),(82,true),(88,false)]
theorem der_26794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26794 :=
  CNF.rup_sound cl_26794 [cl_5182,cl_26790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5182 v h) (hints_cons _ _ _ (der_26790 v h) (by intro d hd; cases hd)))
def cl_26795 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,false),(81,false),(82,false)]
theorem der_26795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26795 :=
  CNF.rup_sound cl_26795 [cl_5190,cl_26781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5190 v h) (hints_cons _ _ _ (der_26781 v h) (by intro d hd; cases hd)))
def cl_26796 : CNF.NClause := [(40,false),(9,true),(69,false),(63,false),(81,false),(82,false),(75,true)]
theorem der_26796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26796 :=
  CNF.rup_sound cl_26796 [cl_5194,cl_26782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5194 v h) (hints_cons _ _ _ (der_26782 v h) (by intro d hd; cases hd)))
def cl_26797 : CNF.NClause := [(40,false),(9,true),(63,false),(75,true),(81,false),(82,false),(88,true)]
theorem der_26797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26797 :=
  CNF.rup_sound cl_26797 [cl_5198,cl_26796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5198 v h) (hints_cons _ _ _ (der_26796 v h) (by intro d hd; cases hd)))
def cl_26798 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(75,false),(63,false),(82,false)]
theorem der_26798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26798 :=
  CNF.rup_sound cl_26798 [cl_5202,cl_26784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5202 v h) (hints_cons _ _ _ (der_26784 v h) (by intro d hd; cases hd)))
def cl_26799 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,false),(81,true),(82,false)]
theorem der_26799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26799 :=
  CNF.rup_sound cl_26799 [cl_5206,cl_26785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5206 v h) (hints_cons _ _ _ (der_26785 v h) (by intro d hd; cases hd)))
def cl_26800 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(63,false),(82,false),(88,true)]
theorem der_26800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26800 :=
  CNF.rup_sound cl_26800 [cl_5210,cl_26798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5210 v h) (hints_cons _ _ _ (der_26798 v h) (by intro d hd; cases hd)))
def cl_26801 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(81,true),(82,false),(88,true)]
theorem der_26801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26801 :=
  CNF.rup_sound cl_26801 [cl_5214,cl_26799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5214 v h) (hints_cons _ _ _ (der_26799 v h) (by intro d hd; cases hd)))
def cl_26802 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,false),(81,false),(82,true)]
theorem der_26802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26802 :=
  CNF.rup_sound cl_26802 [cl_5222,cl_26788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5222 v h) (hints_cons _ _ _ (der_26788 v h) (by intro d hd; cases hd)))
def cl_26803 : CNF.NClause := [(40,false),(9,true),(69,false),(63,false),(81,false),(75,true),(88,true)]
theorem der_26803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26803 :=
  CNF.rup_sound cl_26803 [cl_5226,cl_26796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5226 v h) (hints_cons _ _ _ (der_26796 v h) (by intro d hd; cases hd)))
def cl_26804 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,true),(81,false),(82,true)]
theorem der_26804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26804 :=
  CNF.rup_sound cl_26804 [cl_5230,cl_26794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5230 v h) (hints_cons _ _ _ (der_26794 v h) (by intro d hd; cases hd)))
def cl_26805 : CNF.NClause := [(40,false),(82,true),(9,true),(69,false),(75,false),(63,false),(81,true)]
theorem der_26805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26805 :=
  CNF.rup_sound cl_26805 [cl_5234,cl_26791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5234 v h) (hints_cons _ _ _ (der_26791 v h) (by intro d hd; cases hd)))
def cl_26806 : CNF.NClause := [(40,false),(9,true),(63,false),(75,false),(81,true),(82,true),(88,true)]
theorem der_26806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26806 :=
  CNF.rup_sound cl_26806 [cl_5238,cl_26805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5238 v h) (hints_cons _ _ _ (der_26805 v h) (by intro d hd; cases hd)))
def cl_26807 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(63,false),(82,true),(88,true)]
theorem der_26807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26807 :=
  CNF.rup_sound cl_26807 [cl_5242,cl_26805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5242 v h) (hints_cons _ _ _ (der_26805 v h) (by intro d hd; cases hd)))
def cl_26808 : CNF.NClause := [(40,false),(69,true),(9,true),(63,false),(75,true),(81,true),(82,true)]
theorem der_26808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26808 :=
  CNF.rup_sound cl_26808 [cl_5246,cl_26794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5246 v h) (hints_cons _ _ _ (der_26794 v h) (by intro d hd; cases hd)))
def cl_26809 : CNF.NClause := [(45,false),(14,true),(86,false),(79,false),(72,false),(63,false),(89,false)]
theorem der_26809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26809 :=
  CNF.rup_sound cl_26809 [cl_5766,cl_5762] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5766 v h) (hints_cons _ _ _ (inp_5762 v h) (by intro d hd; cases hd)))
def cl_26810 : CNF.NClause := [(45,false),(14,true),(86,false),(79,false),(63,false),(70,true),(89,false)]
theorem der_26810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26810 :=
  CNF.rup_sound cl_26810 [cl_5774,cl_26809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5774 v h) (hints_cons _ _ _ (der_26809 v h) (by intro d hd; cases hd)))
def cl_26811 : CNF.NClause := [(45,false),(14,true),(63,false),(72,false),(70,true),(86,false),(89,false)]
theorem der_26811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26811 :=
  CNF.rup_sound cl_26811 [cl_5782,cl_26809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5782 v h) (hints_cons _ _ _ (der_26809 v h) (by intro d hd; cases hd)))
def cl_26812 : CNF.NClause := [(45,false),(14,true),(63,false),(72,true),(70,true),(86,false),(89,false)]
theorem der_26812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26812 :=
  CNF.rup_sound cl_26812 [cl_5790,cl_26810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5790 v h) (hints_cons _ _ _ (der_26810 v h) (by intro d hd; cases hd)))
def cl_26813 : CNF.NClause := [(45,false),(14,true),(63,false),(72,false),(79,false),(86,true),(89,false)]
theorem der_26813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26813 :=
  CNF.rup_sound cl_26813 [cl_5798,cl_26765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5798 v h) (hints_cons _ _ _ (der_26765 v h) (by intro d hd; cases hd)))
def cl_26814 : CNF.NClause := [(45,false),(70,true),(14,true),(63,false),(79,false),(86,true),(89,false)]
theorem der_26814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26814 :=
  CNF.rup_sound cl_26814 [cl_5806,cl_26813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5806 v h) (hints_cons _ _ _ (der_26813 v h) (by intro d hd; cases hd)))
def cl_26815 : CNF.NClause := [(45,false),(14,true),(63,false),(72,false),(70,true),(86,true),(89,false)]
theorem der_26815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26815 :=
  CNF.rup_sound cl_26815 [cl_5814,cl_26813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5814 v h) (hints_cons _ _ _ (der_26813 v h) (by intro d hd; cases hd)))
def cl_26816 : CNF.NClause := [(45,false),(79,true),(14,true),(63,false),(70,true),(86,true),(89,false)]
theorem der_26816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26816 :=
  CNF.rup_sound cl_26816 [cl_5822,cl_26815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5822 v h) (hints_cons _ _ _ (der_26815 v h) (by intro d hd; cases hd)))
def cl_26817 : CNF.NClause := [(45,false),(70,true),(14,true),(63,false),(86,false),(72,false),(79,false)]
theorem der_26817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26817 :=
  CNF.rup_sound cl_26817 [cl_5830,cl_26809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5830 v h) (hints_cons _ _ _ (der_26809 v h) (by intro d hd; cases hd)))
def cl_26818 : CNF.NClause := [(45,false),(14,true),(63,false),(89,true),(79,false),(70,true),(86,false)]
theorem der_26818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26818 :=
  CNF.rup_sound cl_26818 [cl_5838,cl_26817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5838 v h) (hints_cons _ _ _ (der_26817 v h) (by intro d hd; cases hd)))
def cl_26819 : CNF.NClause := [(45,false),(14,true),(63,false),(72,false),(70,true),(86,false),(89,true)]
theorem der_26819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26819 :=
  CNF.rup_sound cl_26819 [cl_5846,cl_26817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5846 v h) (hints_cons _ _ _ (der_26817 v h) (by intro d hd; cases hd)))
def cl_26820 : CNF.NClause := [(45,false),(79,true),(14,true),(63,false),(72,true),(70,true),(86,false)]
theorem der_26820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26820 :=
  CNF.rup_sound cl_26820 [cl_5854,cl_26812] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5854 v h) (hints_cons _ _ _ (der_26812 v h) (by intro d hd; cases hd)))
def cl_26821 : CNF.NClause := [(45,false),(70,true),(14,true),(63,false),(72,false),(79,false),(86,true)]
theorem der_26821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26821 :=
  CNF.rup_sound cl_26821 [cl_5862,cl_26813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5862 v h) (hints_cons _ _ _ (der_26813 v h) (by intro d hd; cases hd)))
def cl_26822 : CNF.NClause := [(45,false),(70,true),(14,true),(63,false),(79,false),(86,true),(89,true)]
theorem der_26822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26822 :=
  CNF.rup_sound cl_26822 [cl_5870,cl_26821] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5870 v h) (hints_cons _ _ _ (der_26821 v h) (by intro d hd; cases hd)))
def cl_26823 : CNF.NClause := [(45,false),(79,true),(14,true),(63,false),(72,false),(70,true),(86,true)]
theorem der_26823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26823 :=
  CNF.rup_sound cl_26823 [cl_5878,cl_26816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5878 v h) (hints_cons _ _ _ (der_26816 v h) (by intro d hd; cases hd)))
def cl_26824 : CNF.NClause := [(45,false),(79,true),(14,true),(63,false),(72,true),(70,true),(86,true)]
theorem der_26824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26824 :=
  CNF.rup_sound cl_26824 [cl_5886,cl_26816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5886 v h) (hints_cons _ _ _ (der_26816 v h) (by intro d hd; cases hd)))
def cl_26825 : CNF.NClause := [(50,false),(77,true),(19,false),(71,false),(74,false),(85,false),(63,false)]
theorem der_26825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26825 :=
  CNF.rup_sound cl_26825 [cl_6481,cl_26321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6481 v h) (hints_cons _ _ _ (der_26321 v h) (by intro d hd; cases hd)))
def cl_26826 : CNF.NClause := [(58,false),(69,false),(27,true),(76,false),(85,false),(78,false),(89,false)]
theorem der_26826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26826 :=
  CNF.rup_sound cl_26826 [cl_7426,cl_7428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7426 v h) (hints_cons _ _ _ (inp_7428 v h) (by intro d hd; cases hd)))
def cl_26827 : CNF.NClause := [(58,false),(69,false),(89,false),(85,false),(78,false),(62,true),(76,false)]
theorem der_26827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26827 :=
  CNF.rup_sound cl_26827 [cl_7427,cl_26826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7427 v h) (hints_cons _ _ _ (der_26826 v h) (by intro d hd; cases hd)))
def cl_26828 : CNF.NClause := [(58,false),(69,true),(85,false),(76,false),(62,false),(78,false),(89,false)]
theorem der_26828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26828 :=
  CNF.rup_sound cl_26828 [cl_7430,cl_7429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7430 v h) (hints_cons _ _ _ (inp_7429 v h) (by intro d hd; cases hd)))
def cl_26829 : CNF.NClause := [(58,false),(69,true),(27,false),(89,false),(76,false),(78,false),(85,false)]
theorem der_26829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26829 :=
  CNF.rup_sound cl_26829 [cl_7431,cl_7429] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7431 v h) (hints_cons _ _ _ (inp_7429 v h) (by intro d hd; cases hd)))
def cl_26830 : CNF.NClause := [(58,false),(69,true),(62,true),(76,false),(89,false),(85,false),(78,false)]
theorem der_26830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26830 :=
  CNF.rup_sound cl_26830 [cl_7432,cl_26829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7432 v h) (hints_cons _ _ _ (der_26829 v h) (by intro d hd; cases hd)))
def cl_26831 : CNF.NClause := [(58,false),(69,false),(27,true),(89,false),(85,false),(62,false),(78,false)]
theorem der_26831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26831 :=
  CNF.rup_sound cl_26831 [cl_7434,cl_26826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7434 v h) (hints_cons _ _ _ (der_26826 v h) (by intro d hd; cases hd)))
def cl_26832 : CNF.NClause := [(58,false),(69,false),(27,false),(78,false),(76,true),(85,false),(89,false)]
theorem der_26832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26832 :=
  CNF.rup_sound cl_26832 [cl_7435,cl_7433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7435 v h) (hints_cons _ _ _ (inp_7433 v h) (by intro d hd; cases hd)))
def cl_26833 : CNF.NClause := [(58,false),(69,false),(85,false),(76,true),(62,true),(78,false),(89,false)]
theorem der_26833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26833 :=
  CNF.rup_sound cl_26833 [cl_7436,cl_26832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7436 v h) (hints_cons _ _ _ (der_26832 v h) (by intro d hd; cases hd)))
def cl_26834 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(78,false),(85,false),(89,false)]
theorem der_26834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26834 :=
  CNF.rup_sound cl_26834 [cl_7437,cl_26829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7437 v h) (hints_cons _ _ _ (der_26829 v h) (by intro d hd; cases hd)))
def cl_26835 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(78,false),(85,false),(89,false)]
theorem der_26835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26835 :=
  CNF.rup_sound cl_26835 [cl_7438,cl_26828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7438 v h) (hints_cons _ _ _ (der_26828 v h) (by intro d hd; cases hd)))
def cl_26836 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(78,false),(85,false),(89,false)]
theorem der_26836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26836 :=
  CNF.rup_sound cl_26836 [cl_7439,cl_26829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7439 v h) (hints_cons _ _ _ (der_26829 v h) (by intro d hd; cases hd)))
def cl_26837 : CNF.NClause := [(58,false),(69,true),(62,true),(76,true),(78,false),(85,false),(89,false)]
theorem der_26837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26837 :=
  CNF.rup_sound cl_26837 [cl_7440,cl_26836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7440 v h) (hints_cons _ _ _ (der_26836 v h) (by intro d hd; cases hd)))
def cl_26838 : CNF.NClause := [(58,false),(27,true),(69,false),(76,false),(62,false),(85,false),(89,false)]
theorem der_26838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26838 :=
  CNF.rup_sound cl_26838 [cl_7442,cl_26831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7442 v h) (hints_cons _ _ _ (der_26831 v h) (by intro d hd; cases hd)))
def cl_26839 : CNF.NClause := [(58,false),(27,false),(69,false),(76,false),(78,true),(85,false),(89,false)]
theorem der_26839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26839 :=
  CNF.rup_sound cl_26839 [cl_7443,cl_7441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7443 v h) (hints_cons _ _ _ (inp_7441 v h) (by intro d hd; cases hd)))
def cl_26840 : CNF.NClause := [(58,false),(78,true),(27,true),(69,false),(76,false),(85,false),(89,false)]
theorem der_26840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26840 :=
  CNF.rup_sound cl_26840 [cl_7444,cl_26838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7444 v h) (hints_cons _ _ _ (der_26838 v h) (by intro d hd; cases hd)))
def cl_26841 : CNF.NClause := [(58,false),(27,false),(62,false),(76,false),(78,true),(85,false),(89,false)]
theorem der_26841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26841 :=
  CNF.rup_sound cl_26841 [cl_7445,cl_26839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7445 v h) (hints_cons _ _ _ (der_26839 v h) (by intro d hd; cases hd)))
def cl_26842 : CNF.NClause := [(58,false),(27,true),(62,false),(76,false),(78,true),(85,false),(89,false)]
theorem der_26842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26842 :=
  CNF.rup_sound cl_26842 [cl_7446,cl_26838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7446 v h) (hints_cons _ _ _ (der_26838 v h) (by intro d hd; cases hd)))
def cl_26843 : CNF.NClause := [(58,false),(27,false),(62,true),(76,false),(78,true),(85,false),(89,false)]
theorem der_26843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26843 :=
  CNF.rup_sound cl_26843 [cl_7447,cl_26839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7447 v h) (hints_cons _ _ _ (der_26839 v h) (by intro d hd; cases hd)))
def cl_26844 : CNF.NClause := [(58,false),(27,true),(62,true),(76,false),(78,true),(85,false),(89,false)]
theorem der_26844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26844 :=
  CNF.rup_sound cl_26844 [cl_7448,cl_26840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7448 v h) (hints_cons _ _ _ (der_26840 v h) (by intro d hd; cases hd)))
def cl_26845 : CNF.NClause := [(58,false),(27,false),(69,false),(76,true),(62,false),(85,false),(89,false)]
theorem der_26845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26845 :=
  CNF.rup_sound cl_26845 [cl_7449,cl_26832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7449 v h) (hints_cons _ _ _ (der_26832 v h) (by intro d hd; cases hd)))
def cl_26846 : CNF.NClause := [(58,false),(78,true),(69,false),(76,true),(62,false),(85,false),(89,false)]
theorem der_26846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26846 :=
  CNF.rup_sound cl_26846 [cl_7450,cl_26845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7450 v h) (hints_cons _ _ _ (der_26845 v h) (by intro d hd; cases hd)))
def cl_26847 : CNF.NClause := [(58,false),(62,true),(27,false),(69,false),(76,true),(85,false),(89,false)]
theorem der_26847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26847 :=
  CNF.rup_sound cl_26847 [cl_7451,cl_26832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7451 v h) (hints_cons _ _ _ (der_26832 v h) (by intro d hd; cases hd)))
def cl_26848 : CNF.NClause := [(58,false),(78,true),(27,true),(62,true),(69,false),(85,false),(89,false)]
theorem der_26848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26848 :=
  CNF.rup_sound cl_26848 [cl_7452,cl_26840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7452 v h) (hints_cons _ _ _ (der_26840 v h) (by intro d hd; cases hd)))
def cl_26849 : CNF.NClause := [(58,false),(27,false),(62,false),(76,true),(78,true),(85,false),(89,false)]
theorem der_26849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26849 :=
  CNF.rup_sound cl_26849 [cl_7453,cl_26846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7453 v h) (hints_cons _ _ _ (der_26846 v h) (by intro d hd; cases hd)))
def cl_26850 : CNF.NClause := [(58,false),(27,true),(62,false),(76,true),(78,true),(85,false),(89,false)]
theorem der_26850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26850 :=
  CNF.rup_sound cl_26850 [cl_7454,cl_26846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7454 v h) (hints_cons _ _ _ (der_26846 v h) (by intro d hd; cases hd)))
def cl_26851 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,true),(85,false),(89,false)]
theorem der_26851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26851 :=
  CNF.rup_sound cl_26851 [cl_7455,cl_26836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7455 v h) (hints_cons _ _ _ (der_26836 v h) (by intro d hd; cases hd)))
def cl_26852 : CNF.NClause := [(58,false),(69,true),(27,true),(76,true),(78,true),(85,false),(89,false)]
theorem der_26852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26852 :=
  CNF.rup_sound cl_26852 [cl_7456,cl_26850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7456 v h) (hints_cons _ _ _ (der_26850 v h) (by intro d hd; cases hd)))
def cl_26853 : CNF.NClause := [(58,false),(78,false),(76,false),(62,false),(89,false),(69,false),(85,true)]
theorem der_26853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26853 :=
  CNF.rup_sound cl_26853 [cl_7458,cl_7457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7458 v h) (hints_cons _ _ _ (inp_7457 v h) (by intro d hd; cases hd)))
def cl_26854 : CNF.NClause := [(58,false),(85,true),(27,false),(78,false),(89,false),(69,false),(76,false)]
theorem der_26854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26854 :=
  CNF.rup_sound cl_26854 [cl_7459,cl_7457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7459 v h) (hints_cons _ _ _ (inp_7457 v h) (by intro d hd; cases hd)))
def cl_26855 : CNF.NClause := [(58,false),(62,true),(27,true),(89,false),(69,false),(78,false),(76,false)]
theorem der_26855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26855 :=
  CNF.rup_sound cl_26855 [cl_7460,cl_7428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7460 v h) (hints_cons _ _ _ (inp_7428 v h) (by intro d hd; cases hd)))
def cl_26856 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(76,false),(78,false),(89,false)]
theorem der_26856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26856 :=
  CNF.rup_sound cl_26856 [cl_7461,cl_26829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7461 v h) (hints_cons _ _ _ (der_26829 v h) (by intro d hd; cases hd)))
def cl_26857 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(76,false),(78,false),(89,false)]
theorem der_26857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26857 :=
  CNF.rup_sound cl_26857 [cl_7462,cl_26828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7462 v h) (hints_cons _ _ _ (der_26828 v h) (by intro d hd; cases hd)))
def cl_26858 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,false),(78,false),(89,false)]
theorem der_26858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26858 :=
  CNF.rup_sound cl_26858 [cl_7463,cl_26829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7463 v h) (hints_cons _ _ _ (der_26829 v h) (by intro d hd; cases hd)))
def cl_26859 : CNF.NClause := [(58,false),(69,true),(62,true),(76,false),(78,false),(85,true),(89,false)]
theorem der_26859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26859 :=
  CNF.rup_sound cl_26859 [cl_7464,cl_26858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7464 v h) (hints_cons _ _ _ (der_26858 v h) (by intro d hd; cases hd)))
def cl_26860 : CNF.NClause := [(58,false),(62,false),(27,false),(69,false),(76,true),(89,false),(78,false)]
theorem der_26860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26860 :=
  CNF.rup_sound cl_26860 [cl_7465,cl_7433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7465 v h) (hints_cons _ _ _ (inp_7433 v h) (by intro d hd; cases hd)))
def cl_26861 : CNF.NClause := [(58,false),(62,false),(27,true),(78,false),(89,false),(69,false),(76,true)]
theorem der_26861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26861 :=
  CNF.rup_sound cl_26861 [cl_7466,cl_26831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7466 v h) (hints_cons _ _ _ (der_26831 v h) (by intro d hd; cases hd)))
def cl_26862 : CNF.NClause := [(58,false),(27,false),(78,false),(76,true),(89,false),(69,false),(62,true)]
theorem der_26862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26862 :=
  CNF.rup_sound cl_26862 [cl_7467,cl_26832] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7467 v h) (hints_cons _ _ _ (der_26832 v h) (by intro d hd; cases hd)))
def cl_26863 : CNF.NClause := [(58,false),(27,true),(76,true),(78,false),(85,true),(69,false),(89,false)]
theorem der_26863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26863 :=
  CNF.rup_sound cl_26863 [cl_7468,cl_26861] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7468 v h) (hints_cons _ _ _ (der_26861 v h) (by intro d hd; cases hd)))
def cl_26864 : CNF.NClause := [(58,false),(27,false),(62,false),(76,true),(78,false),(85,true),(89,false)]
theorem der_26864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26864 :=
  CNF.rup_sound cl_26864 [cl_7469,cl_26860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7469 v h) (hints_cons _ _ _ (der_26860 v h) (by intro d hd; cases hd)))
def cl_26865 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(78,false),(85,true),(89,false)]
theorem der_26865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26865 :=
  CNF.rup_sound cl_26865 [cl_7470,cl_26857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7470 v h) (hints_cons _ _ _ (der_26857 v h) (by intro d hd; cases hd)))
def cl_26866 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(78,false),(85,true),(89,false)]
theorem der_26866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26866 :=
  CNF.rup_sound cl_26866 [cl_7471,cl_26858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7471 v h) (hints_cons _ _ _ (der_26858 v h) (by intro d hd; cases hd)))
def cl_26867 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(78,false),(85,true),(89,false)]
theorem der_26867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26867 :=
  CNF.rup_sound cl_26867 [cl_7472,cl_26859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7472 v h) (hints_cons _ _ _ (der_26859 v h) (by intro d hd; cases hd)))
def cl_26868 : CNF.NClause := [(58,false),(27,false),(69,false),(76,false),(62,false),(85,true),(89,false)]
theorem der_26868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26868 :=
  CNF.rup_sound cl_26868 [cl_7473,cl_7457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7473 v h) (hints_cons _ _ _ (inp_7457 v h) (by intro d hd; cases hd)))
def cl_26869 : CNF.NClause := [(58,false),(78,true),(27,true),(69,false),(76,false),(62,false),(89,false)]
theorem der_26869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26869 :=
  CNF.rup_sound cl_26869 [cl_7474,cl_26838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7474 v h) (hints_cons _ _ _ (der_26838 v h) (by intro d hd; cases hd)))
def cl_26870 : CNF.NClause := [(58,false),(27,false),(62,true),(76,false),(78,true),(69,false),(89,false)]
theorem der_26870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26870 :=
  CNF.rup_sound cl_26870 [cl_7475,cl_26839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7475 v h) (hints_cons _ _ _ (der_26839 v h) (by intro d hd; cases hd)))
def cl_26871 : CNF.NClause := [(58,false),(78,true),(62,true),(69,false),(76,false),(85,true),(89,false)]
theorem der_26871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26871 :=
  CNF.rup_sound cl_26871 [cl_7476,cl_26870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7476 v h) (hints_cons _ _ _ (der_26870 v h) (by intro d hd; cases hd)))
def cl_26872 : CNF.NClause := [(58,false),(27,false),(62,false),(76,false),(78,true),(85,true),(89,false)]
theorem der_26872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26872 :=
  CNF.rup_sound cl_26872 [cl_7477,cl_26868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7477 v h) (hints_cons _ _ _ (der_26868 v h) (by intro d hd; cases hd)))
def cl_26873 : CNF.NClause := [(58,false),(69,true),(62,false),(76,false),(78,true),(85,true),(89,false)]
theorem der_26873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26873 :=
  CNF.rup_sound cl_26873 [cl_7478,cl_26872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7478 v h) (hints_cons _ _ _ (der_26872 v h) (by intro d hd; cases hd)))
def cl_26874 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,false),(85,true),(89,false)]
theorem der_26874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26874 :=
  CNF.rup_sound cl_26874 [cl_7479,cl_26858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7479 v h) (hints_cons _ _ _ (der_26858 v h) (by intro d hd; cases hd)))
def cl_26875 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(76,false),(85,true),(89,false)]
theorem der_26875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26875 :=
  CNF.rup_sound cl_26875 [cl_7480,cl_26859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7480 v h) (hints_cons _ _ _ (der_26859 v h) (by intro d hd; cases hd)))
def cl_26876 : CNF.NClause := [(58,false),(78,true),(27,false),(69,false),(76,true),(62,false),(89,false)]
theorem der_26876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26876 :=
  CNF.rup_sound cl_26876 [cl_7481,cl_26845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7481 v h) (hints_cons _ _ _ (der_26845 v h) (by intro d hd; cases hd)))
def cl_26877 : CNF.NClause := [(58,false),(78,true),(27,true),(69,false),(76,true),(62,false),(89,false)]
theorem der_26877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26877 :=
  CNF.rup_sound cl_26877 [cl_7482,cl_26850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7482 v h) (hints_cons _ _ _ (der_26850 v h) (by intro d hd; cases hd)))
def cl_26878 : CNF.NClause := [(58,false),(85,true),(27,false),(62,true),(78,true),(69,false),(89,false)]
theorem der_26878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26878 :=
  CNF.rup_sound cl_26878 [cl_7483,cl_26870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7483 v h) (hints_cons _ _ _ (der_26870 v h) (by intro d hd; cases hd)))
def cl_26879 : CNF.NClause := [(58,false),(27,true),(62,true),(69,false),(76,true),(85,true),(89,false)]
theorem der_26879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26879 :=
  CNF.rup_sound cl_26879 [cl_7484,cl_26863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7484 v h) (hints_cons _ _ _ (der_26863 v h) (by intro d hd; cases hd)))
def cl_26880 : CNF.NClause := [(58,false),(27,false),(62,false),(76,true),(78,true),(85,true),(89,false)]
theorem der_26880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26880 :=
  CNF.rup_sound cl_26880 [cl_7485,cl_26876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7485 v h) (hints_cons _ _ _ (der_26876 v h) (by intro d hd; cases hd)))
def cl_26881 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(76,true),(78,true),(89,false)]
theorem der_26881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26881 :=
  CNF.rup_sound cl_26881 [cl_7486,cl_26850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7486 v h) (hints_cons _ _ _ (der_26850 v h) (by intro d hd; cases hd)))
def cl_26883 : CNF.NClause := [(58,false),(27,true),(62,true),(76,true),(78,true),(85,true),(89,false)]
theorem der_26883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26883 :=
  CNF.rup_sound cl_26883 [cl_7488,cl_26879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7488 v h) (hints_cons _ _ _ (der_26879 v h) (by intro d hd; cases hd)))
def cl_26884 : CNF.NClause := [(58,false),(69,false),(27,true),(78,false),(76,false),(85,false),(62,false)]
theorem der_26884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26884 :=
  CNF.rup_sound cl_26884 [cl_7490,cl_26838] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7490 v h) (hints_cons _ _ _ (der_26838 v h) (by intro d hd; cases hd)))
def cl_26885 : CNF.NClause := [(58,false),(89,true),(27,false),(76,false),(69,false),(85,false),(78,false)]
theorem der_26885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26885 :=
  CNF.rup_sound cl_26885 [cl_7491,cl_7489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7491 v h) (hints_cons _ _ _ (inp_7489 v h) (by intro d hd; cases hd)))
def cl_26886 : CNF.NClause := [(58,false),(69,false),(27,true),(85,false),(78,false),(89,true),(76,false)]
theorem der_26886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26886 :=
  CNF.rup_sound cl_26886 [cl_7492,cl_26884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7492 v h) (hints_cons _ _ _ (der_26884 v h) (by intro d hd; cases hd)))
def cl_26887 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(76,false),(78,false),(85,false)]
theorem der_26887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26887 :=
  CNF.rup_sound cl_26887 [cl_7493,cl_26829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7493 v h) (hints_cons _ _ _ (der_26829 v h) (by intro d hd; cases hd)))
def cl_26888 : CNF.NClause := [(58,false),(69,true),(27,true),(85,false),(76,false),(62,false),(78,false)]
theorem der_26888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26888 :=
  CNF.rup_sound cl_26888 [cl_7494,cl_26857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7494 v h) (hints_cons _ _ _ (der_26857 v h) (by intro d hd; cases hd)))
def cl_26889 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,false),(78,false),(85,false)]
theorem der_26889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26889 :=
  CNF.rup_sound cl_26889 [cl_7495,cl_26858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7495 v h) (hints_cons _ _ _ (der_26858 v h) (by intro d hd; cases hd)))
def cl_26890 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(76,false),(78,false),(85,false)]
theorem der_26890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26890 :=
  CNF.rup_sound cl_26890 [cl_7496,cl_26830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7496 v h) (hints_cons _ _ _ (der_26830 v h) (by intro d hd; cases hd)))
def cl_26891 : CNF.NClause := [(58,false),(89,true),(27,false),(85,false),(62,false),(69,false),(78,false)]
theorem der_26891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26891 :=
  CNF.rup_sound cl_26891 [cl_7497,cl_7489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7497 v h) (hints_cons _ _ _ (inp_7489 v h) (by intro d hd; cases hd)))
def cl_26892 : CNF.NClause := [(58,false),(69,false),(27,true),(89,true),(62,false),(78,false),(85,false)]
theorem der_26892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26892 :=
  CNF.rup_sound cl_26892 [cl_7498,cl_26886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7498 v h) (hints_cons _ _ _ (der_26886 v h) (by intro d hd; cases hd)))
def cl_26893 : CNF.NClause := [(58,false),(27,false),(62,true),(76,true),(69,false),(85,false),(78,false)]
theorem der_26893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26893 :=
  CNF.rup_sound cl_26893 [cl_7499,cl_26833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7499 v h) (hints_cons _ _ _ (der_26833 v h) (by intro d hd; cases hd)))
def cl_26894 : CNF.NClause := [(58,false),(69,false),(27,true),(62,true),(76,true),(78,false),(85,false)]
theorem der_26894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26894 :=
  CNF.rup_sound cl_26894 [cl_7500,cl_26833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7500 v h) (hints_cons _ _ _ (der_26833 v h) (by intro d hd; cases hd)))
def cl_26895 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(76,true),(78,false),(85,false)]
theorem der_26895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26895 :=
  CNF.rup_sound cl_26895 [cl_7501,cl_26834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7501 v h) (hints_cons _ _ _ (der_26834 v h) (by intro d hd; cases hd)))
def cl_26896 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(76,true),(78,false),(85,false)]
theorem der_26896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26896 :=
  CNF.rup_sound cl_26896 [cl_7502,cl_26835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7502 v h) (hints_cons _ _ _ (der_26835 v h) (by intro d hd; cases hd)))
def cl_26897 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,true),(78,false),(85,false)]
theorem der_26897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26897 :=
  CNF.rup_sound cl_26897 [cl_7503,cl_26851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7503 v h) (hints_cons _ _ _ (der_26851 v h) (by intro d hd; cases hd)))
def cl_26898 : CNF.NClause := [(58,false),(69,true),(62,true),(76,true),(78,false),(85,false),(89,true)]
theorem der_26898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26898 :=
  CNF.rup_sound cl_26898 [cl_7504,cl_26897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7504 v h) (hints_cons _ _ _ (der_26897 v h) (by intro d hd; cases hd)))
def cl_26899 : CNF.NClause := [(58,false),(78,true),(27,false),(69,false),(76,false),(62,false),(85,false)]
theorem der_26899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26899 :=
  CNF.rup_sound cl_26899 [cl_7505,cl_26839] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7505 v h) (hints_cons _ _ _ (der_26839 v h) (by intro d hd; cases hd)))
def cl_26900 : CNF.NClause := [(58,false),(27,true),(69,false),(76,false),(62,false),(85,false),(89,true)]
theorem der_26900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26900 :=
  CNF.rup_sound cl_26900 [cl_7506,cl_26884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7506 v h) (hints_cons _ _ _ (der_26884 v h) (by intro d hd; cases hd)))
def cl_26901 : CNF.NClause := [(58,false),(27,false),(62,true),(76,false),(78,true),(85,false),(69,false)]
theorem der_26901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26901 :=
  CNF.rup_sound cl_26901 [cl_7507,cl_26870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7507 v h) (hints_cons _ _ _ (der_26870 v h) (by intro d hd; cases hd)))
def cl_26902 : CNF.NClause := [(58,false),(78,true),(62,true),(69,false),(76,false),(85,false),(89,true)]
theorem der_26902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26902 :=
  CNF.rup_sound cl_26902 [cl_7508,cl_26901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7508 v h) (hints_cons _ _ _ (der_26901 v h) (by intro d hd; cases hd)))
def cl_26903 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(76,false),(78,true),(85,false)]
theorem der_26903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26903 :=
  CNF.rup_sound cl_26903 [cl_7509,cl_26841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7509 v h) (hints_cons _ _ _ (der_26841 v h) (by intro d hd; cases hd)))
def cl_26904 : CNF.NClause := [(58,false),(69,true),(62,false),(76,false),(78,true),(85,false),(89,true)]
theorem der_26904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26904 :=
  CNF.rup_sound cl_26904 [cl_7510,cl_26903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7510 v h) (hints_cons _ _ _ (der_26903 v h) (by intro d hd; cases hd)))
def cl_26905 : CNF.NClause := [(58,false),(69,true),(27,false),(76,false),(78,true),(85,false),(89,true)]
theorem der_26905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26905 :=
  CNF.rup_sound cl_26905 [cl_7511,cl_26903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7511 v h) (hints_cons _ _ _ (der_26903 v h) (by intro d hd; cases hd)))
def cl_26906 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(76,false),(78,true),(85,false)]
theorem der_26906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26906 :=
  CNF.rup_sound cl_26906 [cl_7512,cl_26844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7512 v h) (hints_cons _ _ _ (der_26844 v h) (by intro d hd; cases hd)))
def cl_26907 : CNF.NClause := [(58,false),(78,true),(27,false),(69,false),(62,false),(85,false),(89,true)]
theorem der_26907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26907 :=
  CNF.rup_sound cl_26907 [cl_7513,cl_26899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7513 v h) (hints_cons _ _ _ (der_26899 v h) (by intro d hd; cases hd)))
def cl_26908 : CNF.NClause := [(58,false),(78,true),(27,true),(69,false),(76,true),(62,false),(85,false)]
theorem der_26908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26908 :=
  CNF.rup_sound cl_26908 [cl_7514,cl_26850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7514 v h) (hints_cons _ _ _ (der_26850 v h) (by intro d hd; cases hd)))
def cl_26909 : CNF.NClause := [(58,false),(89,true),(27,false),(62,true),(78,true),(85,false),(69,false)]
theorem der_26909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26909 :=
  CNF.rup_sound cl_26909 [cl_7515,cl_26902] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7515 v h) (hints_cons _ _ _ (der_26902 v h) (by intro d hd; cases hd)))
def cl_26910 : CNF.NClause := [(58,false),(78,true),(27,true),(69,false),(76,true),(85,false),(89,true)]
theorem der_26910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26910 :=
  CNF.rup_sound cl_26910 [cl_7516,cl_26908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7516 v h) (hints_cons _ _ _ (der_26908 v h) (by intro d hd; cases hd)))
def cl_26911 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(78,true),(85,false),(89,true)]
theorem der_26911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26911 :=
  CNF.rup_sound cl_26911 [cl_7517,cl_26903] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7517 v h) (hints_cons _ _ _ (der_26903 v h) (by intro d hd; cases hd)))
def cl_26912 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(76,true),(78,true),(85,false)]
theorem der_26912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26912 :=
  CNF.rup_sound cl_26912 [cl_7518,cl_26850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7518 v h) (hints_cons _ _ _ (der_26850 v h) (by intro d hd; cases hd)))
def cl_26914 : CNF.NClause := [(58,false),(27,true),(62,true),(76,true),(78,true),(85,false),(89,true)]
theorem der_26914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26914 :=
  CNF.rup_sound cl_26914 [cl_7520,cl_26910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7520 v h) (hints_cons _ _ _ (der_26910 v h) (by intro d hd; cases hd)))
def cl_26915 : CNF.NClause := [(58,false),(78,false),(27,false),(85,true),(76,false),(62,false),(69,false)]
theorem der_26915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26915 :=
  CNF.rup_sound cl_26915 [cl_7521,cl_7457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7521 v h) (hints_cons _ _ _ (inp_7457 v h) (by intro d hd; cases hd)))
def cl_26916 : CNF.NClause := [(58,false),(78,false),(27,true),(89,true),(76,false),(62,false),(69,false)]
theorem der_26916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26916 :=
  CNF.rup_sound cl_26916 [cl_7522,cl_26884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7522 v h) (hints_cons _ _ _ (der_26884 v h) (by intro d hd; cases hd)))
def cl_26917 : CNF.NClause := [(58,false),(69,false),(27,false),(76,false),(62,true),(85,true),(78,false)]
theorem der_26917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26917 :=
  CNF.rup_sound cl_26917 [cl_7523,cl_26854] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7523 v h) (hints_cons _ _ _ (der_26854 v h) (by intro d hd; cases hd)))
def cl_26918 : CNF.NClause := [(58,false),(62,true),(27,true),(78,false),(69,false),(76,false),(85,true)]
theorem der_26918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26918 :=
  CNF.rup_sound cl_26918 [cl_7524,cl_26855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7524 v h) (hints_cons _ _ _ (der_26855 v h) (by intro d hd; cases hd)))
def cl_26919 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(76,false),(78,false),(85,true)]
theorem der_26919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26919 :=
  CNF.rup_sound cl_26919 [cl_7525,cl_26856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7525 v h) (hints_cons _ _ _ (der_26856 v h) (by intro d hd; cases hd)))
def cl_26920 : CNF.NClause := [(58,false),(69,true),(62,false),(76,false),(78,false),(85,true),(89,true)]
theorem der_26920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26920 :=
  CNF.rup_sound cl_26920 [cl_7526,cl_26919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7526 v h) (hints_cons _ _ _ (der_26919 v h) (by intro d hd; cases hd)))
def cl_26921 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,false),(78,false),(85,true)]
theorem der_26921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26921 :=
  CNF.rup_sound cl_26921 [cl_7527,cl_26858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7527 v h) (hints_cons _ _ _ (der_26858 v h) (by intro d hd; cases hd)))
def cl_26922 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(76,false),(78,false),(85,true)]
theorem der_26922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26922 :=
  CNF.rup_sound cl_26922 [cl_7528,cl_26859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7528 v h) (hints_cons _ _ _ (der_26859 v h) (by intro d hd; cases hd)))
def cl_26923 : CNF.NClause := [(58,false),(89,true),(27,false),(69,false),(62,false),(76,true),(78,false)]
theorem der_26923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26923 :=
  CNF.rup_sound cl_26923 [cl_7529,cl_26891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7529 v h) (hints_cons _ _ _ (der_26891 v h) (by intro d hd; cases hd)))
def cl_26924 : CNF.NClause := [(58,false),(69,false),(27,true),(62,false),(85,true),(76,true),(78,false)]
theorem der_26924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26924 :=
  CNF.rup_sound cl_26924 [cl_7530,cl_26863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7530 v h) (hints_cons _ _ _ (der_26863 v h) (by intro d hd; cases hd)))
def cl_26925 : CNF.NClause := [(58,false),(85,true),(27,false),(62,true),(76,true),(69,false),(78,false)]
theorem der_26925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26925 :=
  CNF.rup_sound cl_26925 [cl_7531,cl_26862] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7531 v h) (hints_cons _ _ _ (der_26862 v h) (by intro d hd; cases hd)))
def cl_26926 : CNF.NClause := [(58,false),(62,true),(27,true),(85,true),(69,false),(78,false),(76,true)]
theorem der_26926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26926 :=
  CNF.rup_sound cl_26926 [cl_7532,cl_26879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7532 v h) (hints_cons _ _ _ (der_26879 v h) (by intro d hd; cases hd)))
def cl_26927 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(78,false),(85,true),(89,true)]
theorem der_26927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26927 :=
  CNF.rup_sound cl_26927 [cl_7533,cl_26919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7533 v h) (hints_cons _ _ _ (der_26919 v h) (by intro d hd; cases hd)))
def cl_26928 : CNF.NClause := [(58,false),(27,true),(62,false),(76,true),(78,false),(85,true),(89,true)]
theorem der_26928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26928 :=
  CNF.rup_sound cl_26928 [cl_7534,cl_26924] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7534 v h) (hints_cons _ _ _ (der_26924 v h) (by intro d hd; cases hd)))
def cl_26929 : CNF.NClause := [(58,false),(69,true),(27,false),(62,true),(76,true),(78,false),(89,true)]
theorem der_26929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26929 :=
  CNF.rup_sound cl_26929 [cl_7535,cl_26897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7535 v h) (hints_cons _ _ _ (der_26897 v h) (by intro d hd; cases hd)))
def cl_26930 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(78,false),(85,true),(89,true)]
theorem der_26930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26930 :=
  CNF.rup_sound cl_26930 [cl_7536,cl_26922] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7536 v h) (hints_cons _ _ _ (der_26922 v h) (by intro d hd; cases hd)))
def cl_26931 : CNF.NClause := [(58,false),(78,true),(27,false),(69,false),(76,false),(62,false),(89,true)]
theorem der_26931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26931 :=
  CNF.rup_sound cl_26931 [cl_7537,cl_26899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7537 v h) (hints_cons _ _ _ (der_26899 v h) (by intro d hd; cases hd)))
def cl_26932 : CNF.NClause := [(58,false),(27,true),(69,false),(76,false),(62,false),(85,true),(89,true)]
theorem der_26932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26932 :=
  CNF.rup_sound cl_26932 [cl_7538,cl_26916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7538 v h) (hints_cons _ _ _ (der_26916 v h) (by intro d hd; cases hd)))
def cl_26933 : CNF.NClause := [(58,false),(85,true),(27,false),(62,true),(76,false),(78,true),(69,false)]
theorem der_26933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26933 :=
  CNF.rup_sound cl_26933 [cl_7539,cl_26870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7539 v h) (hints_cons _ _ _ (der_26870 v h) (by intro d hd; cases hd)))
def cl_26934 : CNF.NClause := [(58,false),(78,true),(27,true),(62,true),(69,false),(76,false),(85,true)]
theorem der_26934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26934 :=
  CNF.rup_sound cl_26934 [cl_7540,cl_26871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7540 v h) (hints_cons _ _ _ (der_26871 v h) (by intro d hd; cases hd)))
def cl_26935 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(76,false),(85,true),(89,true)]
theorem der_26935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26935 :=
  CNF.rup_sound cl_26935 [cl_7541,cl_26919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7541 v h) (hints_cons _ _ _ (der_26919 v h) (by intro d hd; cases hd)))
def cl_26936 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(76,false),(78,true),(85,true)]
theorem der_26936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26936 :=
  CNF.rup_sound cl_26936 [cl_7542,cl_26873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7542 v h) (hints_cons _ _ _ (der_26873 v h) (by intro d hd; cases hd)))
def cl_26937 : CNF.NClause := [(58,false),(69,true),(27,false),(76,false),(78,true),(85,true),(89,true)]
theorem der_26937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26937 :=
  CNF.rup_sound cl_26937 [cl_7543,cl_26935] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7543 v h) (hints_cons _ _ _ (der_26935 v h) (by intro d hd; cases hd)))
def cl_26938 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(76,false),(85,true),(89,true)]
theorem der_26938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26938 :=
  CNF.rup_sound cl_26938 [cl_7544,cl_26930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7544 v h) (hints_cons _ _ _ (der_26930 v h) (by intro d hd; cases hd)))
def cl_26939 : CNF.NClause := [(58,false),(78,true),(27,false),(69,false),(62,false),(85,true),(89,true)]
theorem der_26939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26939 :=
  CNF.rup_sound cl_26939 [cl_7545,cl_26931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7545 v h) (hints_cons _ _ _ (der_26931 v h) (by intro d hd; cases hd)))
def cl_26940 : CNF.NClause := [(58,false),(78,true),(27,true),(69,false),(76,true),(62,false),(89,true)]
theorem der_26940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26940 :=
  CNF.rup_sound cl_26940 [cl_7546,cl_26908] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7546 v h) (hints_cons _ _ _ (der_26908 v h) (by intro d hd; cases hd)))
def cl_26942 : CNF.NClause := [(58,false),(78,true),(27,true),(62,true),(69,false),(76,true),(85,true)]
theorem der_26942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26942 :=
  CNF.rup_sound cl_26942 [cl_7548,cl_26879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7548 v h) (hints_cons _ _ _ (der_26879 v h) (by intro d hd; cases hd)))
def cl_26943 : CNF.NClause := [(58,false),(27,false),(62,false),(76,true),(78,true),(85,true),(89,true)]
theorem der_26943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26943 :=
  CNF.rup_sound cl_26943 [cl_7549,cl_26939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7549 v h) (hints_cons _ _ _ (der_26939 v h) (by intro d hd; cases hd)))
def cl_26944 : CNF.NClause := [(58,false),(69,true),(27,true),(62,false),(76,true),(78,true),(85,true)]
theorem der_26944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26944 :=
  CNF.rup_sound cl_26944 [cl_7550,cl_26881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7550 v h) (hints_cons _ _ _ (der_26881 v h) (by intro d hd; cases hd)))
def cl_26946 : CNF.NClause := [(58,false),(69,true),(27,true),(62,true),(76,true),(85,true),(89,true)]
theorem der_26946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26946 :=
  CNF.rup_sound cl_26946 [cl_7552,cl_26930] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7552 v h) (hints_cons _ _ _ (der_26930 v h) (by intro d hd; cases hd)))
def cl_26947 : CNF.NClause := [(54,false),(65,true),(74,false),(67,false),(81,false),(83,false),(89,false)]
theorem der_26947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26947 :=
  CNF.rup_sound cl_26947 [cl_6916,cl_6915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6916 v h) (hints_cons _ _ _ (inp_6915 v h) (by intro d hd; cases hd)))
def cl_26948 : CNF.NClause := [(54,false),(23,true),(65,false),(89,false),(74,false),(83,false),(81,false)]
theorem der_26948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26948 :=
  CNF.rup_sound cl_26948 [cl_6918,cl_6914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6918 v h) (hints_cons _ _ _ (inp_6914 v h) (by intro d hd; cases hd)))
def cl_26949 : CNF.NClause := [(54,false),(65,true),(23,false),(74,false),(81,false),(83,false),(89,false)]
theorem der_26949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26949 :=
  CNF.rup_sound cl_26949 [cl_6919,cl_6915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6919 v h) (hints_cons _ _ _ (inp_6915 v h) (by intro d hd; cases hd)))
def cl_26950 : CNF.NClause := [(54,false),(65,true),(67,true),(74,false),(81,false),(83,false),(89,false)]
theorem der_26950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26950 :=
  CNF.rup_sound cl_26950 [cl_6920,cl_26949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6920 v h) (hints_cons _ _ _ (der_26949 v h) (by intro d hd; cases hd)))
def cl_26951 : CNF.NClause := [(54,false),(23,true),(81,false),(83,false),(89,false),(65,false),(67,false)]
theorem der_26951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26951 :=
  CNF.rup_sound cl_26951 [cl_6922,cl_26948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6922 v h) (hints_cons _ _ _ (der_26948 v h) (by intro d hd; cases hd)))
def cl_26952 : CNF.NClause := [(54,false),(65,true),(23,false),(67,false),(83,false),(89,false),(81,false)]
theorem der_26952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26952 :=
  CNF.rup_sound cl_26952 [cl_6923,cl_6915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6923 v h) (hints_cons _ _ _ (inp_6915 v h) (by intro d hd; cases hd)))
def cl_26953 : CNF.NClause := [(54,false),(65,true),(74,true),(67,false),(83,false),(89,false),(81,false)]
theorem der_26953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26953 :=
  CNF.rup_sound cl_26953 [cl_6924,cl_26952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6924 v h) (hints_cons _ _ _ (der_26952 v h) (by intro d hd; cases hd)))
def cl_26954 : CNF.NClause := [(54,false),(74,true),(83,false),(23,false),(81,false),(65,false),(89,false)]
theorem der_26954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26954 :=
  CNF.rup_sound cl_26954 [cl_6925,cl_6921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6925 v h) (hints_cons _ _ _ (inp_6921 v h) (by intro d hd; cases hd)))
def cl_26955 : CNF.NClause := [(54,false),(23,true),(67,true),(81,false),(89,false),(83,false),(65,false)]
theorem der_26955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26955 :=
  CNF.rup_sound cl_26955 [cl_6926,cl_26948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6926 v h) (hints_cons _ _ _ (der_26948 v h) (by intro d hd; cases hd)))
def cl_26956 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(81,false),(83,false),(89,false)]
theorem der_26956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26956 :=
  CNF.rup_sound cl_26956 [cl_6927,cl_26949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6927 v h) (hints_cons _ _ _ (der_26949 v h) (by intro d hd; cases hd)))
def cl_26957 : CNF.NClause := [(54,false),(65,true),(23,true),(74,true),(81,false),(83,false),(89,false)]
theorem der_26957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26957 :=
  CNF.rup_sound cl_26957 [cl_6928,cl_26953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6928 v h) (hints_cons _ _ _ (der_26953 v h) (by intro d hd; cases hd)))
def cl_26958 : CNF.NClause := [(54,false),(81,true),(67,false),(74,false),(65,false),(83,false),(89,false)]
theorem der_26958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26958 :=
  CNF.rup_sound cl_26958 [cl_6930,cl_6929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6930 v h) (hints_cons _ _ _ (inp_6929 v h) (by intro d hd; cases hd)))
def cl_26959 : CNF.NClause := [(54,false),(81,true),(23,false),(67,false),(74,false),(83,false),(89,false)]
theorem der_26959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26959 :=
  CNF.rup_sound cl_26959 [cl_6931,cl_6929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6931 v h) (hints_cons _ _ _ (inp_6929 v h) (by intro d hd; cases hd)))
def cl_26960 : CNF.NClause := [(54,false),(81,true),(65,true),(74,false),(67,false),(83,false),(89,false)]
theorem der_26960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26960 :=
  CNF.rup_sound cl_26960 [cl_6932,cl_26959] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6932 v h) (hints_cons _ _ _ (der_26959 v h) (by intro d hd; cases hd)))
def cl_26961 : CNF.NClause := [(54,false),(81,true),(65,false),(23,false),(74,false),(83,false),(89,false)]
theorem der_26961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26961 :=
  CNF.rup_sound cl_26961 [cl_6933,cl_6929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6933 v h) (hints_cons _ _ _ (inp_6929 v h) (by intro d hd; cases hd)))
def cl_26962 : CNF.NClause := [(54,false),(81,true),(65,false),(67,true),(74,false),(83,false),(89,false)]
theorem der_26962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26962 :=
  CNF.rup_sound cl_26962 [cl_6934,cl_26961] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6934 v h) (hints_cons _ _ _ (der_26961 v h) (by intro d hd; cases hd)))
def cl_26963 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(74,false),(83,false),(89,false)]
theorem der_26963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26963 :=
  CNF.rup_sound cl_26963 [cl_6935,cl_26949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6935 v h) (hints_cons _ _ _ (der_26949 v h) (by intro d hd; cases hd)))
def cl_26964 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,false),(83,false),(89,false)]
theorem der_26964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26964 :=
  CNF.rup_sound cl_26964 [cl_6936,cl_26950] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6936 v h) (hints_cons _ _ _ (der_26950 v h) (by intro d hd; cases hd)))
def cl_26965 : CNF.NClause := [(54,false),(65,false),(67,false),(23,false),(74,true),(83,false),(89,false)]
theorem der_26965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26965 :=
  CNF.rup_sound cl_26965 [cl_6937,cl_6921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6937 v h) (hints_cons _ _ _ (inp_6921 v h) (by intro d hd; cases hd)))
def cl_26966 : CNF.NClause := [(54,false),(23,true),(67,false),(65,false),(74,true),(83,false),(89,false)]
theorem der_26966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26966 :=
  CNF.rup_sound cl_26966 [cl_6938,cl_26951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6938 v h) (hints_cons _ _ _ (der_26951 v h) (by intro d hd; cases hd)))
def cl_26967 : CNF.NClause := [(54,false),(81,true),(23,false),(65,true),(67,false),(83,false),(89,false)]
theorem der_26967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26967 :=
  CNF.rup_sound cl_26967 [cl_6939,cl_26960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6939 v h) (hints_cons _ _ _ (der_26960 v h) (by intro d hd; cases hd)))
def cl_26968 : CNF.NClause := [(54,false),(81,true),(65,true),(67,false),(74,true),(83,false),(89,false)]
theorem der_26968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26968 :=
  CNF.rup_sound cl_26968 [cl_6940,cl_26967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6940 v h) (hints_cons _ _ _ (der_26967 v h) (by intro d hd; cases hd)))
def cl_26969 : CNF.NClause := [(54,false),(65,false),(23,false),(74,true),(67,true),(83,false),(89,false)]
theorem der_26969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26969 :=
  CNF.rup_sound cl_26969 [cl_6941,cl_26954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6941 v h) (hints_cons _ _ _ (der_26954 v h) (by intro d hd; cases hd)))
def cl_26970 : CNF.NClause := [(54,false),(81,true),(23,true),(65,false),(74,true),(83,false),(89,false)]
theorem der_26970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26970 :=
  CNF.rup_sound cl_26970 [cl_6942,cl_26966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6942 v h) (hints_cons _ _ _ (der_26966 v h) (by intro d hd; cases hd)))
def cl_26971 : CNF.NClause := [(54,false),(65,true),(23,false),(74,true),(81,true),(83,false),(89,false)]
theorem der_26971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26971 :=
  CNF.rup_sound cl_26971 [cl_6943,cl_26967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6943 v h) (hints_cons _ _ _ (der_26967 v h) (by intro d hd; cases hd)))
def cl_26972 : CNF.NClause := [(54,false),(65,true),(67,true),(74,true),(81,true),(83,false),(89,false)]
theorem der_26972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26972 :=
  CNF.rup_sound cl_26972 [cl_6944,cl_26971] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6944 v h) (hints_cons _ _ _ (der_26971 v h) (by intro d hd; cases hd)))
def cl_26973 : CNF.NClause := [(54,false),(23,true),(67,false),(74,false),(81,false),(65,false),(89,false)]
theorem der_26973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26973 :=
  CNF.rup_sound cl_26973 [cl_6946,cl_26948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6946 v h) (hints_cons _ _ _ (der_26948 v h) (by intro d hd; cases hd)))
def cl_26974 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(89,false)]
theorem der_26974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26974 :=
  CNF.rup_sound cl_26974 [cl_6947,cl_6915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6947 v h) (hints_cons _ _ _ (inp_6915 v h) (by intro d hd; cases hd)))
def cl_26975 : CNF.NClause := [(54,false),(83,true),(65,true),(74,false),(81,false),(67,false),(89,false)]
theorem der_26975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26975 :=
  CNF.rup_sound cl_26975 [cl_6948,cl_26974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6948 v h) (hints_cons _ _ _ (der_26974 v h) (by intro d hd; cases hd)))
def cl_26976 : CNF.NClause := [(54,false),(65,false),(23,false),(67,true),(81,false),(74,false),(89,false)]
theorem der_26976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26976 :=
  CNF.rup_sound cl_26976 [cl_6949,cl_6917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6949 v h) (hints_cons _ _ _ (inp_6917 v h) (by intro d hd; cases hd)))
def cl_26977 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(81,false),(74,false),(89,false)]
theorem der_26977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26977 :=
  CNF.rup_sound cl_26977 [cl_6950,cl_26948] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6950 v h) (hints_cons _ _ _ (der_26948 v h) (by intro d hd; cases hd)))
def cl_26978 : CNF.NClause := [(54,false),(23,false),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem der_26978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26978 :=
  CNF.rup_sound cl_26978 [cl_6951,cl_26976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6951 v h) (hints_cons _ _ _ (der_26976 v h) (by intro d hd; cases hd)))
def cl_26979 : CNF.NClause := [(54,false),(65,true),(67,true),(74,false),(81,false),(83,true),(89,false)]
theorem der_26979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26979 :=
  CNF.rup_sound cl_26979 [cl_6952,cl_26978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6952 v h) (hints_cons _ _ _ (der_26978 v h) (by intro d hd; cases hd)))
def cl_26980 : CNF.NClause := [(54,false),(65,false),(67,false),(23,false),(81,false),(74,true),(89,false)]
theorem der_26980 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26980 :=
  CNF.rup_sound cl_26980 [cl_6953,cl_26965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6953 v h) (hints_cons _ _ _ (der_26965 v h) (by intro d hd; cases hd)))
def cl_26981 : CNF.NClause := [(54,false),(23,true),(67,false),(65,false),(81,false),(74,true),(89,false)]
theorem der_26981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26981 :=
  CNF.rup_sound cl_26981 [cl_6954,cl_26951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6954 v h) (hints_cons _ _ _ (der_26951 v h) (by intro d hd; cases hd)))
def cl_26982 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(81,false),(74,true),(89,false)]
theorem der_26982 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26982 :=
  CNF.rup_sound cl_26982 [cl_6955,cl_26952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6955 v h) (hints_cons _ _ _ (der_26952 v h) (by intro d hd; cases hd)))
def cl_26983 : CNF.NClause := [(54,false),(83,true),(65,true),(67,false),(81,false),(74,true),(89,false)]
theorem der_26983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26983 :=
  CNF.rup_sound cl_26983 [cl_6956,cl_26982] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6956 v h) (hints_cons _ _ _ (der_26982 v h) (by intro d hd; cases hd)))
def cl_26984 : CNF.NClause := [(54,false),(83,true),(65,false),(23,false),(67,true),(81,false),(89,false)]
theorem der_26984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26984 :=
  CNF.rup_sound cl_26984 [cl_6957,cl_26978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6957 v h) (hints_cons _ _ _ (der_26978 v h) (by intro d hd; cases hd)))
def cl_26985 : CNF.NClause := [(54,false),(83,true),(23,true),(65,false),(74,true),(81,false),(89,false)]
theorem der_26985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26985 :=
  CNF.rup_sound cl_26985 [cl_6958,cl_26981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6958 v h) (hints_cons _ _ _ (der_26981 v h) (by intro d hd; cases hd)))
def cl_26986 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(81,false),(83,true),(89,false)]
theorem der_26986 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26986 :=
  CNF.rup_sound cl_26986 [cl_6959,cl_26978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6959 v h) (hints_cons _ _ _ (der_26978 v h) (by intro d hd; cases hd)))
def cl_26987 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(81,false),(83,true),(89,false)]
theorem der_26987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26987 :=
  CNF.rup_sound cl_26987 [cl_6960,cl_26979] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6960 v h) (hints_cons _ _ _ (der_26979 v h) (by intro d hd; cases hd)))
def cl_26988 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(23,false),(83,true),(89,false)]
theorem der_26988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26988 :=
  CNF.rup_sound cl_26988 [cl_6961,cl_6945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6961 v h) (hints_cons _ _ _ (inp_6945 v h) (by intro d hd; cases hd)))
def cl_26989 : CNF.NClause := [(54,false),(23,true),(67,false),(74,false),(65,false),(81,true),(89,false)]
theorem der_26989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26989 :=
  CNF.rup_sound cl_26989 [cl_6962,cl_26958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6962 v h) (hints_cons _ _ _ (der_26958 v h) (by intro d hd; cases hd)))
def cl_26990 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(89,false)]
theorem der_26990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26990 :=
  CNF.rup_sound cl_26990 [cl_6963,cl_26967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6963 v h) (hints_cons _ _ _ (der_26967 v h) (by intro d hd; cases hd)))
def cl_26991 : CNF.NClause := [(54,false),(83,true),(65,true),(74,false),(67,false),(81,true),(89,false)]
theorem der_26991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26991 :=
  CNF.rup_sound cl_26991 [cl_6964,cl_26990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6964 v h) (hints_cons _ _ _ (der_26990 v h) (by intro d hd; cases hd)))
def cl_26992 : CNF.NClause := [(54,false),(83,true),(65,false),(23,false),(67,true),(74,false),(89,false)]
theorem der_26992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26992 :=
  CNF.rup_sound cl_26992 [cl_6965,cl_26978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6965 v h) (hints_cons _ _ _ (der_26978 v h) (by intro d hd; cases hd)))
def cl_26993 : CNF.NClause := [(54,false),(83,true),(65,false),(67,true),(74,false),(81,true),(89,false)]
theorem der_26993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26993 :=
  CNF.rup_sound cl_26993 [cl_6966,cl_26992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6966 v h) (hints_cons _ _ _ (der_26992 v h) (by intro d hd; cases hd)))
def cl_26995 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,false),(83,true),(89,false)]
theorem der_26995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26995 :=
  CNF.rup_sound cl_26995 [cl_6968,cl_26987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6968 v h) (hints_cons _ _ _ (der_26987 v h) (by intro d hd; cases hd)))
def cl_26996 : CNF.NClause := [(54,false),(65,false),(67,false),(23,false),(74,true),(81,true),(89,false)]
theorem der_26996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26996 :=
  CNF.rup_sound cl_26996 [cl_6969,cl_26965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6969 v h) (hints_cons _ _ _ (der_26965 v h) (by intro d hd; cases hd)))
def cl_26997 : CNF.NClause := [(54,false),(23,true),(67,false),(65,false),(74,true),(81,true),(89,false)]
theorem der_26997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26997 :=
  CNF.rup_sound cl_26997 [cl_6970,cl_26966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6970 v h) (hints_cons _ _ _ (der_26966 v h) (by intro d hd; cases hd)))
def cl_26999 : CNF.NClause := [(54,false),(83,true),(23,true),(65,true),(67,false),(81,true),(89,false)]
theorem der_26999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_26999 :=
  CNF.rup_sound cl_26999 [cl_6972,cl_26991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6972 v h) (hints_cons _ _ _ (der_26991 v h) (by intro d hd; cases hd)))
def cl_27000 : CNF.NClause := [(54,false),(83,true),(65,false),(23,false),(74,true),(67,true),(89,false)]
theorem der_27000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27000 :=
  CNF.rup_sound cl_27000 [cl_6973,cl_26984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6973 v h) (hints_cons _ _ _ (der_26984 v h) (by intro d hd; cases hd)))
def cl_27001 : CNF.NClause := [(54,false),(83,true),(65,false),(74,true),(67,true),(81,true),(89,false)]
theorem der_27001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27001 :=
  CNF.rup_sound cl_27001 [cl_6974,cl_27000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6974 v h) (hints_cons _ _ _ (der_27000 v h) (by intro d hd; cases hd)))
def cl_27003 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,true),(83,true),(89,false)]
theorem der_27003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27003 :=
  CNF.rup_sound cl_27003 [cl_6976,cl_26987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6976 v h) (hints_cons _ _ _ (der_26987 v h) (by intro d hd; cases hd)))
def cl_27004 : CNF.NClause := [(54,false),(67,false),(23,true),(81,false),(74,false),(65,false),(83,false)]
theorem der_27004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27004 :=
  CNF.rup_sound cl_27004 [cl_6978,cl_6914] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6978 v h) (hints_cons _ _ _ (inp_6914 v h) (by intro d hd; cases hd)))
def cl_27005 : CNF.NClause := [(54,false),(65,true),(23,false),(67,false),(74,false),(83,false),(81,false)]
theorem der_27005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27005 :=
  CNF.rup_sound cl_27005 [cl_6979,cl_6915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6979 v h) (hints_cons _ _ _ (inp_6915 v h) (by intro d hd; cases hd)))
def cl_27006 : CNF.NClause := [(54,false),(23,true),(81,false),(74,false),(89,true),(83,false),(67,false)]
theorem der_27006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27006 :=
  CNF.rup_sound cl_27006 [cl_6980,cl_27004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6980 v h) (hints_cons _ _ _ (der_27004 v h) (by intro d hd; cases hd)))
def cl_27007 : CNF.NClause := [(54,false),(67,true),(65,false),(23,false),(74,false),(83,false),(81,false)]
theorem der_27007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27007 :=
  CNF.rup_sound cl_27007 [cl_6981,cl_6917] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6981 v h) (hints_cons _ _ _ (inp_6917 v h) (by intro d hd; cases hd)))
def cl_27008 : CNF.NClause := [(54,false),(67,true),(23,true),(74,false),(65,false),(81,false),(83,false)]
theorem der_27008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27008 :=
  CNF.rup_sound cl_27008 [cl_6982,cl_26955] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6982 v h) (hints_cons _ _ _ (der_26955 v h) (by intro d hd; cases hd)))
def cl_27009 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(74,false),(81,false),(83,false)]
theorem der_27009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27009 :=
  CNF.rup_sound cl_27009 [cl_6983,cl_26949] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6983 v h) (hints_cons _ _ _ (der_26949 v h) (by intro d hd; cases hd)))
def cl_27010 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,false),(81,false),(83,false)]
theorem der_27010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27010 :=
  CNF.rup_sound cl_27010 [cl_6984,cl_26964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6984 v h) (hints_cons _ _ _ (der_26964 v h) (by intro d hd; cases hd)))
def cl_27011 : CNF.NClause := [(54,false),(74,true),(65,false),(23,false),(81,false),(67,false),(83,false)]
theorem der_27011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27011 :=
  CNF.rup_sound cl_27011 [cl_6985,cl_6921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6985 v h) (hints_cons _ _ _ (inp_6921 v h) (by intro d hd; cases hd)))
def cl_27012 : CNF.NClause := [(54,false),(74,true),(81,false),(67,false),(65,false),(83,false),(89,true)]
theorem der_27012 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27012 :=
  CNF.rup_sound cl_27012 [cl_6986,cl_27011] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6986 v h) (hints_cons _ _ _ (der_27011 v h) (by intro d hd; cases hd)))
def cl_27013 : CNF.NClause := [(54,false),(23,false),(74,true),(67,false),(81,false),(83,false),(89,true)]
theorem der_27013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27013 :=
  CNF.rup_sound cl_27013 [cl_6987,cl_27012] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6987 v h) (hints_cons _ _ _ (der_27012 v h) (by intro d hd; cases hd)))
def cl_27014 : CNF.NClause := [(54,false),(74,true),(89,true),(67,false),(65,true),(83,false),(81,false)]
theorem der_27014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27014 :=
  CNF.rup_sound cl_27014 [cl_6988,cl_27013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6988 v h) (hints_cons _ _ _ (der_27013 v h) (by intro d hd; cases hd)))
def cl_27015 : CNF.NClause := [(54,false),(74,true),(65,false),(23,false),(89,true),(83,false),(81,false)]
theorem der_27015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27015 :=
  CNF.rup_sound cl_27015 [cl_6989,cl_27013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6989 v h) (hints_cons _ _ _ (der_27013 v h) (by intro d hd; cases hd)))
def cl_27016 : CNF.NClause := [(54,false),(23,true),(65,false),(89,true),(67,true),(83,false),(81,false)]
theorem der_27016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27016 :=
  CNF.rup_sound cl_27016 [cl_6990,cl_27008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6990 v h) (hints_cons _ _ _ (der_27008 v h) (by intro d hd; cases hd)))
def cl_27017 : CNF.NClause := [(54,false),(65,true),(23,false),(74,true),(81,false),(83,false),(89,true)]
theorem der_27017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27017 :=
  CNF.rup_sound cl_27017 [cl_6991,cl_27013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6991 v h) (hints_cons _ _ _ (der_27013 v h) (by intro d hd; cases hd)))
def cl_27018 : CNF.NClause := [(54,false),(65,true),(67,true),(74,true),(81,false),(83,false),(89,true)]
theorem der_27018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27018 :=
  CNF.rup_sound cl_27018 [cl_6992,cl_27017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6992 v h) (hints_cons _ _ _ (der_27017 v h) (by intro d hd; cases hd)))
def cl_27019 : CNF.NClause := [(54,false),(81,true),(65,false),(67,false),(74,false),(23,false),(83,false)]
theorem der_27019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27019 :=
  CNF.rup_sound cl_27019 [cl_6993,cl_6929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6993 v h) (hints_cons _ _ _ (inp_6929 v h) (by intro d hd; cases hd)))
def cl_27020 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(83,false),(89,true)]
theorem der_27020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27020 :=
  CNF.rup_sound cl_27020 [cl_6994,cl_27004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6994 v h) (hints_cons _ _ _ (der_27004 v h) (by intro d hd; cases hd)))
def cl_27021 : CNF.NClause := [(54,false),(81,true),(23,false),(65,true),(67,false),(74,false),(83,false)]
theorem der_27021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27021 :=
  CNF.rup_sound cl_27021 [cl_6995,cl_26967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6995 v h) (hints_cons _ _ _ (der_26967 v h) (by intro d hd; cases hd)))
def cl_27022 : CNF.NClause := [(54,false),(81,true),(23,true),(65,true),(74,false),(67,false),(83,false)]
theorem der_27022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27022 :=
  CNF.rup_sound cl_27022 [cl_6996,cl_26960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6996 v h) (hints_cons _ _ _ (der_26960 v h) (by intro d hd; cases hd)))
def cl_27023 : CNF.NClause := [(54,false),(81,true),(65,false),(23,false),(74,false),(83,false),(89,true)]
theorem der_27023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27023 :=
  CNF.rup_sound cl_27023 [cl_6997,cl_27019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6997 v h) (hints_cons _ _ _ (der_27019 v h) (by intro d hd; cases hd)))
def cl_27024 : CNF.NClause := [(54,false),(81,true),(65,false),(67,true),(74,false),(83,false),(89,true)]
theorem der_27024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27024 :=
  CNF.rup_sound cl_27024 [cl_6998,cl_27023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6998 v h) (hints_cons _ _ _ (der_27023 v h) (by intro d hd; cases hd)))
def cl_27025 : CNF.NClause := [(54,false),(23,false),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem der_27025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27025 :=
  CNF.rup_sound cl_27025 [cl_6999,cl_27023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6999 v h) (hints_cons _ _ _ (der_27023 v h) (by intro d hd; cases hd)))
def cl_27026 : CNF.NClause := [(54,false),(65,true),(67,true),(74,false),(81,true),(83,false),(89,true)]
theorem der_27026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27026 :=
  CNF.rup_sound cl_27026 [cl_7000,cl_27025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7000 v h) (hints_cons _ _ _ (der_27025 v h) (by intro d hd; cases hd)))
def cl_27027 : CNF.NClause := [(54,false),(65,false),(67,false),(23,false),(74,true),(83,false),(89,true)]
theorem der_27027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27027 :=
  CNF.rup_sound cl_27027 [cl_7001,cl_27013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7001 v h) (hints_cons _ _ _ (der_27013 v h) (by intro d hd; cases hd)))
def cl_27028 : CNF.NClause := [(54,false),(81,true),(23,true),(65,false),(74,true),(67,false),(83,false)]
theorem der_27028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27028 :=
  CNF.rup_sound cl_27028 [cl_7002,cl_26966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7002 v h) (hints_cons _ _ _ (der_26966 v h) (by intro d hd; cases hd)))
def cl_27029 : CNF.NClause := [(54,false),(81,true),(23,false),(65,true),(67,false),(74,true),(83,false)]
theorem der_27029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27029 :=
  CNF.rup_sound cl_27029 [cl_7003,cl_26967] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7003 v h) (hints_cons _ _ _ (der_26967 v h) (by intro d hd; cases hd)))
def cl_27030 : CNF.NClause := [(54,false),(81,true),(23,true),(65,true),(67,false),(74,true),(83,false)]
theorem der_27030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27030 :=
  CNF.rup_sound cl_27030 [cl_7004,cl_26968] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7004 v h) (hints_cons _ _ _ (der_26968 v h) (by intro d hd; cases hd)))
def cl_27031 : CNF.NClause := [(54,false),(81,true),(65,false),(23,false),(67,true),(83,false),(89,true)]
theorem der_27031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27031 :=
  CNF.rup_sound cl_27031 [cl_7005,cl_27025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7005 v h) (hints_cons _ _ _ (der_27025 v h) (by intro d hd; cases hd)))
def cl_27032 : CNF.NClause := [(54,false),(81,true),(23,true),(65,false),(74,true),(83,false),(89,true)]
theorem der_27032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27032 :=
  CNF.rup_sound cl_27032 [cl_7006,cl_27028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7006 v h) (hints_cons _ _ _ (der_27028 v h) (by intro d hd; cases hd)))
def cl_27033 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(81,true),(83,false),(89,true)]
theorem der_27033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27033 :=
  CNF.rup_sound cl_27033 [cl_7007,cl_27025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7007 v h) (hints_cons _ _ _ (der_27025 v h) (by intro d hd; cases hd)))
def cl_27034 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(81,true),(83,false),(89,true)]
theorem der_27034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27034 :=
  CNF.rup_sound cl_27034 [cl_7008,cl_27026] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7008 v h) (hints_cons _ _ _ (der_27026 v h) (by intro d hd; cases hd)))
def cl_27035 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(23,false),(81,false),(89,true)]
theorem der_27035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27035 :=
  CNF.rup_sound cl_27035 [cl_7009,cl_6977] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7009 v h) (hints_cons _ _ _ (inp_6977 v h) (by intro d hd; cases hd)))
def cl_27036 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(81,false),(74,false),(89,true)]
theorem der_27036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27036 :=
  CNF.rup_sound cl_27036 [cl_7010,cl_27006] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7010 v h) (hints_cons _ _ _ (der_27006 v h) (by intro d hd; cases hd)))
def cl_27037 : CNF.NClause := [(54,false),(83,true),(23,false),(65,true),(67,false),(74,false),(81,false)]
theorem der_27037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27037 :=
  CNF.rup_sound cl_27037 [cl_7011,cl_26974] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7011 v h) (hints_cons _ _ _ (der_26974 v h) (by intro d hd; cases hd)))
def cl_27038 : CNF.NClause := [(54,false),(83,true),(65,true),(74,false),(81,false),(67,false),(89,true)]
theorem der_27038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27038 :=
  CNF.rup_sound cl_27038 [cl_7012,cl_27037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7012 v h) (hints_cons _ _ _ (der_27037 v h) (by intro d hd; cases hd)))
def cl_27039 : CNF.NClause := [(54,false),(83,true),(65,false),(23,false),(67,true),(81,false),(74,false)]
theorem der_27039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27039 :=
  CNF.rup_sound cl_27039 [cl_7013,cl_26978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7013 v h) (hints_cons _ _ _ (der_26978 v h) (by intro d hd; cases hd)))
def cl_27040 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(81,false),(74,false),(89,true)]
theorem der_27040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27040 :=
  CNF.rup_sound cl_27040 [cl_7014,cl_27016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7014 v h) (hints_cons _ _ _ (der_27016 v h) (by intro d hd; cases hd)))
def cl_27041 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(74,false),(81,false),(83,true)]
theorem der_27041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27041 :=
  CNF.rup_sound cl_27041 [cl_7015,cl_26978] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7015 v h) (hints_cons _ _ _ (der_26978 v h) (by intro d hd; cases hd)))
def cl_27042 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,false),(81,false),(83,true)]
theorem der_27042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27042 :=
  CNF.rup_sound cl_27042 [cl_7016,cl_26987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7016 v h) (hints_cons _ _ _ (der_26987 v h) (by intro d hd; cases hd)))
def cl_27043 : CNF.NClause := [(54,false),(65,false),(67,false),(23,false),(81,false),(74,true),(89,true)]
theorem der_27043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27043 :=
  CNF.rup_sound cl_27043 [cl_7017,cl_27013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7017 v h) (hints_cons _ _ _ (der_27013 v h) (by intro d hd; cases hd)))
def cl_27044 : CNF.NClause := [(54,false),(83,true),(23,true),(65,false),(74,true),(81,false),(67,false)]
theorem der_27044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27044 :=
  CNF.rup_sound cl_27044 [cl_7018,cl_26981] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7018 v h) (hints_cons _ _ _ (der_26981 v h) (by intro d hd; cases hd)))
def cl_27045 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(81,false),(74,true),(89,true)]
theorem der_27045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27045 :=
  CNF.rup_sound cl_27045 [cl_7019,cl_27013] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7019 v h) (hints_cons _ _ _ (der_27013 v h) (by intro d hd; cases hd)))
def cl_27046 : CNF.NClause := [(54,false),(83,true),(23,true),(65,true),(67,false),(81,false),(89,true)]
theorem der_27046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27046 :=
  CNF.rup_sound cl_27046 [cl_7020,cl_27038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7020 v h) (hints_cons _ _ _ (der_27038 v h) (by intro d hd; cases hd)))
def cl_27047 : CNF.NClause := [(54,false),(83,true),(65,false),(23,false),(74,true),(67,true),(81,false)]
theorem der_27047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27047 :=
  CNF.rup_sound cl_27047 [cl_7021,cl_27000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7021 v h) (hints_cons _ _ _ (der_27000 v h) (by intro d hd; cases hd)))
def cl_27048 : CNF.NClause := [(54,false),(83,true),(23,true),(65,false),(74,true),(81,false),(89,true)]
theorem der_27048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27048 :=
  CNF.rup_sound cl_27048 [cl_7022,cl_27044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7022 v h) (hints_cons _ _ _ (der_27044 v h) (by intro d hd; cases hd)))
def cl_27050 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,true),(81,false),(83,true)]
theorem der_27050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27050 :=
  CNF.rup_sound cl_27050 [cl_7024,cl_26987] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7024 v h) (hints_cons _ _ _ (der_26987 v h) (by intro d hd; cases hd)))
def cl_27051 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(23,false),(83,true),(89,true)]
theorem der_27051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27051 :=
  CNF.rup_sound cl_27051 [cl_7025,cl_27035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7025 v h) (hints_cons _ _ _ (der_27035 v h) (by intro d hd; cases hd)))
def cl_27052 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(89,true)]
theorem der_27052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27052 :=
  CNF.rup_sound cl_27052 [cl_7026,cl_27020] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7026 v h) (hints_cons _ _ _ (der_27020 v h) (by intro d hd; cases hd)))
def cl_27053 : CNF.NClause := [(54,false),(83,true),(23,false),(65,true),(67,false),(74,false),(89,true)]
theorem der_27053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27053 :=
  CNF.rup_sound cl_27053 [cl_7027,cl_27037] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7027 v h) (hints_cons _ _ _ (der_27037 v h) (by intro d hd; cases hd)))
def cl_27054 : CNF.NClause := [(54,false),(83,true),(23,true),(65,true),(74,false),(67,false),(89,true)]
theorem der_27054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27054 :=
  CNF.rup_sound cl_27054 [cl_7028,cl_27038] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7028 v h) (hints_cons _ _ _ (der_27038 v h) (by intro d hd; cases hd)))
def cl_27055 : CNF.NClause := [(54,false),(65,false),(23,false),(67,true),(74,false),(81,true),(89,true)]
theorem der_27055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27055 :=
  CNF.rup_sound cl_27055 [cl_7029,cl_27025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7029 v h) (hints_cons _ _ _ (der_27025 v h) (by intro d hd; cases hd)))
def cl_27056 : CNF.NClause := [(54,false),(23,true),(65,false),(67,true),(74,false),(81,true),(89,true)]
theorem der_27056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27056 :=
  CNF.rup_sound cl_27056 [cl_7030,cl_27024] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7030 v h) (hints_cons _ _ _ (der_27024 v h) (by intro d hd; cases hd)))
def cl_27057 : CNF.NClause := [(54,false),(65,true),(23,false),(67,true),(74,false),(81,true),(89,true)]
theorem der_27057 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27057 :=
  CNF.rup_sound cl_27057 [cl_7031,cl_27025] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7031 v h) (hints_cons _ _ _ (der_27025 v h) (by intro d hd; cases hd)))
def cl_27058 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,false),(81,true),(89,true)]
theorem der_27058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27058 :=
  CNF.rup_sound cl_27058 [cl_7032,cl_27034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7032 v h) (hints_cons _ _ _ (der_27034 v h) (by intro d hd; cases hd)))
def cl_27059 : CNF.NClause := [(54,false),(65,false),(67,false),(23,false),(74,true),(81,true),(89,true)]
theorem der_27059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27059 :=
  CNF.rup_sound cl_27059 [cl_7033,cl_27027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7033 v h) (hints_cons _ _ _ (der_27027 v h) (by intro d hd; cases hd)))
def cl_27060 : CNF.NClause := [(54,false),(83,true),(23,true),(65,false),(74,true),(67,false),(89,true)]
theorem der_27060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27060 :=
  CNF.rup_sound cl_27060 [cl_7034,cl_27044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7034 v h) (hints_cons _ _ _ (der_27044 v h) (by intro d hd; cases hd)))
def cl_27062 : CNF.NClause := [(54,false),(83,true),(23,true),(65,true),(67,false),(81,true),(89,true)]
theorem der_27062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27062 :=
  CNF.rup_sound cl_27062 [cl_7036,cl_27054] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7036 v h) (hints_cons _ _ _ (der_27054 v h) (by intro d hd; cases hd)))
def cl_27063 : CNF.NClause := [(54,false),(83,true),(65,false),(23,false),(74,true),(67,true),(81,true)]
theorem der_27063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27063 :=
  CNF.rup_sound cl_27063 [cl_7037,cl_27000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7037 v h) (hints_cons _ _ _ (der_27000 v h) (by intro d hd; cases hd)))
def cl_27064 : CNF.NClause := [(54,false),(83,true),(65,false),(74,true),(67,true),(81,true),(89,true)]
theorem der_27064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27064 :=
  CNF.rup_sound cl_27064 [cl_7038,cl_27063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7038 v h) (hints_cons _ _ _ (der_27063 v h) (by intro d hd; cases hd)))
def cl_27066 : CNF.NClause := [(54,false),(65,true),(23,true),(67,true),(74,true),(81,true),(89,true)]
theorem der_27066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27066 :=
  CNF.rup_sound cl_27066 [cl_7040,cl_27034] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7040 v h) (hints_cons _ _ _ (der_27034 v h) (by intro d hd; cases hd)))
def cl_27067 : CNF.NClause := [(40,false),(88,false),(82,false),(63,true),(75,false),(69,false),(81,false)]
theorem der_27067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27067 :=
  CNF.rup_sound cl_27067 [cl_5124,cl_5123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5124 v h) (hints_cons _ _ _ (inp_5123 v h) (by intro d hd; cases hd)))
def cl_27068 : CNF.NClause := [(40,false),(69,true),(63,false),(75,false),(81,false),(82,false),(88,false)]
theorem der_27068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27068 :=
  CNF.rup_sound cl_27068 [cl_5125,cl_26781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5125 v h) (hints_cons _ _ _ (der_26781 v h) (by intro d hd; cases hd)))
def cl_27069 : CNF.NClause := [(40,false),(9,false),(63,true),(75,false),(81,false),(82,false),(88,false)]
theorem der_27069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27069 :=
  CNF.rup_sound cl_27069 [cl_5127,cl_5123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5127 v h) (hints_cons _ _ _ (inp_5123 v h) (by intro d hd; cases hd)))
def cl_27070 : CNF.NClause := [(40,false),(9,true),(63,true),(75,false),(81,false),(82,false),(88,false)]
theorem der_27070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27070 :=
  CNF.rup_sound cl_27070 [cl_5128,cl_27067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5128 v h) (hints_cons _ _ _ (der_27067 v h) (by intro d hd; cases hd)))
def cl_27071 : CNF.NClause := [(40,false),(75,true),(88,false),(69,false),(63,false),(82,false),(81,false)]
theorem der_27071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27071 :=
  CNF.rup_sound cl_27071 [cl_5129,cl_26796] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5129 v h) (hints_cons _ _ _ (der_26796 v h) (by intro d hd; cases hd)))
def cl_27072 : CNF.NClause := [(40,false),(75,true),(9,false),(69,false),(81,false),(82,false),(88,false)]
theorem der_27072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27072 :=
  CNF.rup_sound cl_27072 [cl_5131,cl_27071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5131 v h) (hints_cons _ _ _ (der_27071 v h) (by intro d hd; cases hd)))
def cl_27073 : CNF.NClause := [(40,false),(75,true),(9,true),(88,false),(69,false),(82,false),(81,false)]
theorem der_27073 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27073 :=
  CNF.rup_sound cl_27073 [cl_5132,cl_27071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5132 v h) (hints_cons _ _ _ (der_27071 v h) (by intro d hd; cases hd)))
def cl_27074 : CNF.NClause := [(40,false),(9,false),(63,false),(75,true),(81,false),(82,false),(88,false)]
theorem der_27074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27074 :=
  CNF.rup_sound cl_27074 [cl_5133,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5133 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_27075 : CNF.NClause := [(40,false),(9,false),(63,true),(75,true),(81,false),(82,false),(88,false)]
theorem der_27075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27075 :=
  CNF.rup_sound cl_27075 [cl_5135,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5135 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_27076 : CNF.NClause := [(40,false),(9,true),(63,true),(75,true),(81,false),(82,false),(88,false)]
theorem der_27076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27076 :=
  CNF.rup_sound cl_27076 [cl_5136,cl_27073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5136 v h) (hints_cons _ _ _ (der_27073 v h) (by intro d hd; cases hd)))
def cl_27077 : CNF.NClause := [(40,false),(81,true),(69,false),(75,false),(63,false),(82,false),(88,false)]
theorem der_27077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27077 :=
  CNF.rup_sound cl_27077 [cl_5137,cl_26798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5137 v h) (hints_cons _ _ _ (der_26798 v h) (by intro d hd; cases hd)))
def cl_27078 : CNF.NClause := [(40,false),(81,true),(9,false),(69,false),(75,false),(82,false),(88,false)]
theorem der_27078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27078 :=
  CNF.rup_sound cl_27078 [cl_5139,cl_27077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5139 v h) (hints_cons _ _ _ (der_27077 v h) (by intro d hd; cases hd)))
def cl_27079 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(75,false),(82,false),(88,false)]
theorem der_27079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27079 :=
  CNF.rup_sound cl_27079 [cl_5140,cl_26798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5140 v h) (hints_cons _ _ _ (der_26798 v h) (by intro d hd; cases hd)))
def cl_27080 : CNF.NClause := [(40,false),(9,false),(63,false),(75,false),(81,true),(82,false),(88,false)]
theorem der_27080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27080 :=
  CNF.rup_sound cl_27080 [cl_5141,cl_27078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5141 v h) (hints_cons _ _ _ (der_27078 v h) (by intro d hd; cases hd)))
def cl_27081 : CNF.NClause := [(40,false),(9,false),(63,true),(75,false),(81,true),(82,false),(88,false)]
theorem der_27081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27081 :=
  CNF.rup_sound cl_27081 [cl_5143,cl_27078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5143 v h) (hints_cons _ _ _ (der_27078 v h) (by intro d hd; cases hd)))
def cl_27082 : CNF.NClause := [(40,false),(69,true),(9,true),(75,false),(81,true),(82,false),(88,false)]
theorem der_27082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27082 :=
  CNF.rup_sound cl_27082 [cl_5144,cl_26785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5144 v h) (hints_cons _ _ _ (der_26785 v h) (by intro d hd; cases hd)))
def cl_27083 : CNF.NClause := [(40,false),(9,false),(69,false),(63,false),(75,true),(82,false),(88,false)]
theorem der_27083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27083 :=
  CNF.rup_sound cl_27083 [cl_5145,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5145 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_27084 : CNF.NClause := [(40,false),(9,false),(69,false),(75,true),(63,true),(82,false),(88,false)]
theorem der_27084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27084 :=
  CNF.rup_sound cl_27084 [cl_5147,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5147 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_27085 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,true),(82,false),(88,false)]
theorem der_27085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27085 :=
  CNF.rup_sound cl_27085 [cl_5148,cl_27073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5148 v h) (hints_cons _ _ _ (der_27073 v h) (by intro d hd; cases hd)))
def cl_27086 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,true),(82,false),(88,false)]
theorem der_27086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27086 :=
  CNF.rup_sound cl_27086 [cl_5149,cl_27074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5149 v h) (hints_cons _ _ _ (der_27074 v h) (by intro d hd; cases hd)))
def cl_27087 : CNF.NClause := [(40,false),(69,true),(9,false),(75,true),(81,true),(82,false),(88,false)]
theorem der_27087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27087 :=
  CNF.rup_sound cl_27087 [cl_5151,cl_27086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5151 v h) (hints_cons _ _ _ (der_27086 v h) (by intro d hd; cases hd)))
def cl_27088 : CNF.NClause := [(40,false),(69,true),(63,true),(75,true),(81,true),(82,false),(88,false)]
theorem der_27088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27088 :=
  CNF.rup_sound cl_27088 [cl_5152,cl_27087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5152 v h) (hints_cons _ _ _ (der_27087 v h) (by intro d hd; cases hd)))
def cl_27089 : CNF.NClause := [(40,false),(9,true),(82,true),(69,false),(63,false),(75,false),(88,false)]
theorem der_27089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27089 :=
  CNF.rup_sound cl_27089 [cl_5154,cl_26792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5154 v h) (hints_cons _ _ _ (der_26792 v h) (by intro d hd; cases hd)))
def cl_27090 : CNF.NClause := [(40,false),(82,true),(9,false),(69,false),(75,false),(81,false),(88,false)]
theorem der_27090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27090 :=
  CNF.rup_sound cl_27090 [cl_5155,cl_5153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5155 v h) (hints_cons _ _ _ (inp_5153 v h) (by intro d hd; cases hd)))
def cl_27091 : CNF.NClause := [(40,false),(82,true),(9,true),(75,false),(69,false),(81,false),(88,false)]
theorem der_27091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27091 :=
  CNF.rup_sound cl_27091 [cl_5156,cl_27089] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5156 v h) (hints_cons _ _ _ (der_27089 v h) (by intro d hd; cases hd)))
def cl_27092 : CNF.NClause := [(40,false),(69,true),(63,false),(75,false),(81,false),(82,true),(88,false)]
theorem der_27092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27092 :=
  CNF.rup_sound cl_27092 [cl_5157,cl_26802] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5157 v h) (hints_cons _ _ _ (der_26802 v h) (by intro d hd; cases hd)))
def cl_27093 : CNF.NClause := [(40,false),(69,true),(9,false),(75,false),(81,false),(82,true),(88,false)]
theorem der_27093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27093 :=
  CNF.rup_sound cl_27093 [cl_5159,cl_27092] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5159 v h) (hints_cons _ _ _ (der_27092 v h) (by intro d hd; cases hd)))
def cl_27094 : CNF.NClause := [(40,false),(69,true),(63,true),(75,false),(81,false),(82,true),(88,false)]
theorem der_27094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27094 :=
  CNF.rup_sound cl_27094 [cl_5160,cl_27093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5160 v h) (hints_cons _ _ _ (der_27093 v h) (by intro d hd; cases hd)))
def cl_27095 : CNF.NClause := [(40,false),(9,false),(63,false),(69,false),(81,false),(75,true),(88,false)]
theorem der_27095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27095 :=
  CNF.rup_sound cl_27095 [cl_5161,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5161 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_27096 : CNF.NClause := [(40,false),(9,false),(69,false),(75,true),(81,false),(63,true),(88,false)]
theorem der_27096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27096 :=
  CNF.rup_sound cl_27096 [cl_5163,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5163 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_27097 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(81,false),(75,true),(88,false)]
theorem der_27097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27097 :=
  CNF.rup_sound cl_27097 [cl_5164,cl_27073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5164 v h) (hints_cons _ _ _ (der_27073 v h) (by intro d hd; cases hd)))
def cl_27098 : CNF.NClause := [(40,false),(69,true),(63,false),(75,true),(81,false),(82,true),(88,false)]
theorem der_27098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27098 :=
  CNF.rup_sound cl_27098 [cl_5165,cl_26794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5165 v h) (hints_cons _ _ _ (der_26794 v h) (by intro d hd; cases hd)))
def cl_27099 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(81,false),(82,true),(88,false)]
theorem der_27099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27099 :=
  CNF.rup_sound cl_27099 [cl_5167,cl_27093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5167 v h) (hints_cons _ _ _ (der_27093 v h) (by intro d hd; cases hd)))
def cl_27100 : CNF.NClause := [(40,false),(69,true),(63,true),(75,true),(81,false),(82,true),(88,false)]
theorem der_27100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27100 :=
  CNF.rup_sound cl_27100 [cl_5168,cl_27099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5168 v h) (hints_cons _ _ _ (der_27099 v h) (by intro d hd; cases hd)))
def cl_27101 : CNF.NClause := [(40,false),(9,false),(63,false),(75,false),(69,false),(81,true),(88,false)]
theorem der_27101 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27101 :=
  CNF.rup_sound cl_27101 [cl_5169,cl_27078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5169 v h) (hints_cons _ _ _ (der_27078 v h) (by intro d hd; cases hd)))
def cl_27102 : CNF.NClause := [(40,false),(9,false),(69,false),(75,false),(63,true),(81,true),(88,false)]
theorem der_27102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27102 :=
  CNF.rup_sound cl_27102 [cl_5171,cl_27078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5171 v h) (hints_cons _ _ _ (der_27078 v h) (by intro d hd; cases hd)))
def cl_27103 : CNF.NClause := [(40,false),(82,true),(63,true),(69,false),(75,false),(81,true),(88,false)]
theorem der_27103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27103 :=
  CNF.rup_sound cl_27103 [cl_5172,cl_27102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5172 v h) (hints_cons _ _ _ (der_27102 v h) (by intro d hd; cases hd)))
def cl_27104 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,false),(81,true),(88,false)]
theorem der_27104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27104 :=
  CNF.rup_sound cl_27104 [cl_5173,cl_27080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5173 v h) (hints_cons _ _ _ (der_27080 v h) (by intro d hd; cases hd)))
def cl_27105 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,false),(82,true),(88,false)]
theorem der_27105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27105 :=
  CNF.rup_sound cl_27105 [cl_5175,cl_27099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5175 v h) (hints_cons _ _ _ (der_27099 v h) (by intro d hd; cases hd)))
def cl_27106 : CNF.NClause := [(40,false),(69,true),(9,true),(63,true),(75,false),(81,true),(88,false)]
theorem der_27106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27106 :=
  CNF.rup_sound cl_27106 [cl_5176,cl_27082] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5176 v h) (hints_cons _ _ _ (der_27082 v h) (by intro d hd; cases hd)))
def cl_27107 : CNF.NClause := [(40,false),(81,true),(9,false),(63,false),(69,false),(75,true),(88,false)]
theorem der_27107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27107 :=
  CNF.rup_sound cl_27107 [cl_5177,cl_27083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5177 v h) (hints_cons _ _ _ (der_27083 v h) (by intro d hd; cases hd)))
def cl_27108 : CNF.NClause := [(40,false),(82,true),(9,false),(69,false),(63,true),(81,true),(88,false)]
theorem der_27108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27108 :=
  CNF.rup_sound cl_27108 [cl_5179,cl_27102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5179 v h) (hints_cons _ _ _ (der_27102 v h) (by intro d hd; cases hd)))
def cl_27109 : CNF.NClause := [(40,false),(81,true),(63,true),(69,false),(75,true),(82,true),(88,false)]
theorem der_27109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27109 :=
  CNF.rup_sound cl_27109 [cl_5180,cl_27108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5180 v h) (hints_cons _ _ _ (der_27108 v h) (by intro d hd; cases hd)))
def cl_27110 : CNF.NClause := [(40,false),(69,true),(63,false),(75,true),(81,true),(82,true),(88,false)]
theorem der_27110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27110 :=
  CNF.rup_sound cl_27110 [cl_5181,cl_26794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5181 v h) (hints_cons _ _ _ (der_26794 v h) (by intro d hd; cases hd)))
def cl_27111 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,true),(82,true),(88,false)]
theorem der_27111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27111 :=
  CNF.rup_sound cl_27111 [cl_5183,cl_27099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5183 v h) (hints_cons _ _ _ (der_27099 v h) (by intro d hd; cases hd)))
def cl_27112 : CNF.NClause := [(40,false),(69,true),(9,true),(75,true),(81,true),(82,true),(88,false)]
theorem der_27112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27112 :=
  CNF.rup_sound cl_27112 [cl_5184,cl_26794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5184 v h) (hints_cons _ _ _ (der_26794 v h) (by intro d hd; cases hd)))
def cl_27113 : CNF.NClause := [(40,false),(88,true),(9,true),(69,false),(81,false),(63,false),(82,false)]
theorem der_27113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27113 :=
  CNF.rup_sound cl_27113 [cl_5186,cl_26797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5186 v h) (hints_cons _ _ _ (der_26797 v h) (by intro d hd; cases hd)))
def cl_27114 : CNF.NClause := [(40,false),(88,true),(9,false),(69,false),(75,false),(81,false),(82,false)]
theorem der_27114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27114 :=
  CNF.rup_sound cl_27114 [cl_5187,cl_5185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5187 v h) (hints_cons _ _ _ (inp_5185 v h) (by intro d hd; cases hd)))
def cl_27115 : CNF.NClause := [(40,false),(88,true),(9,true),(69,false),(75,false),(81,false),(82,false)]
theorem der_27115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27115 :=
  CNF.rup_sound cl_27115 [cl_5188,cl_27113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5188 v h) (hints_cons _ _ _ (der_27113 v h) (by intro d hd; cases hd)))
def cl_27116 : CNF.NClause := [(40,false),(9,false),(63,false),(75,false),(81,false),(82,false),(69,true)]
theorem der_27116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27116 :=
  CNF.rup_sound cl_27116 [cl_5189,cl_27068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5189 v h) (hints_cons _ _ _ (der_27068 v h) (by intro d hd; cases hd)))
def cl_27117 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,false),(81,false),(82,false)]
theorem der_27117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27117 :=
  CNF.rup_sound cl_27117 [cl_5191,cl_27069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5191 v h) (hints_cons _ _ _ (der_27069 v h) (by intro d hd; cases hd)))
def cl_27118 : CNF.NClause := [(40,false),(69,true),(63,true),(75,false),(81,false),(82,false),(88,true)]
theorem der_27118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27118 :=
  CNF.rup_sound cl_27118 [cl_5192,cl_27117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5192 v h) (hints_cons _ _ _ (der_27117 v h) (by intro d hd; cases hd)))
def cl_27119 : CNF.NClause := [(40,false),(88,true),(63,false),(69,false),(81,false),(82,false),(75,true)]
theorem der_27119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27119 :=
  CNF.rup_sound cl_27119 [cl_5193,cl_26797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5193 v h) (hints_cons _ _ _ (der_26797 v h) (by intro d hd; cases hd)))
def cl_27120 : CNF.NClause := [(40,false),(88,true),(9,false),(69,false),(81,false),(82,false),(63,true)]
theorem der_27120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27120 :=
  CNF.rup_sound cl_27120 [cl_5195,cl_27114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5195 v h) (hints_cons _ _ _ (der_27114 v h) (by intro d hd; cases hd)))
def cl_27121 : CNF.NClause := [(40,false),(88,true),(9,true),(69,false),(81,false),(82,false),(75,true)]
theorem der_27121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27121 :=
  CNF.rup_sound cl_27121 [cl_5196,cl_26797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5196 v h) (hints_cons _ _ _ (der_26797 v h) (by intro d hd; cases hd)))
def cl_27122 : CNF.NClause := [(40,false),(88,true),(63,false),(75,true),(81,false),(82,false),(69,true)]
theorem der_27122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27122 :=
  CNF.rup_sound cl_27122 [cl_5197,cl_26797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5197 v h) (hints_cons _ _ _ (der_26797 v h) (by intro d hd; cases hd)))
def cl_27123 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(81,false),(82,false),(88,true)]
theorem der_27123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27123 :=
  CNF.rup_sound cl_27123 [cl_5199,cl_27117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5199 v h) (hints_cons _ _ _ (der_27117 v h) (by intro d hd; cases hd)))
def cl_27124 : CNF.NClause := [(40,false),(69,true),(63,true),(75,true),(81,false),(82,false),(88,true)]
theorem der_27124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27124 :=
  CNF.rup_sound cl_27124 [cl_5200,cl_27123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5200 v h) (hints_cons _ _ _ (der_27123 v h) (by intro d hd; cases hd)))
def cl_27125 : CNF.NClause := [(40,false),(81,true),(63,false),(75,false),(69,false),(82,false),(88,true)]
theorem der_27125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27125 :=
  CNF.rup_sound cl_27125 [cl_5201,cl_26798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5201 v h) (hints_cons _ _ _ (der_26798 v h) (by intro d hd; cases hd)))
def cl_27126 : CNF.NClause := [(40,false),(81,true),(9,false),(69,false),(75,false),(63,true),(82,false)]
theorem der_27126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27126 :=
  CNF.rup_sound cl_27126 [cl_5203,cl_27078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5203 v h) (hints_cons _ _ _ (der_27078 v h) (by intro d hd; cases hd)))
def cl_27127 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(75,false),(82,false),(88,true)]
theorem der_27127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27127 :=
  CNF.rup_sound cl_27127 [cl_5204,cl_26798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5204 v h) (hints_cons _ _ _ (der_26798 v h) (by intro d hd; cases hd)))
def cl_27128 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,false),(81,true),(82,false)]
theorem der_27128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27128 :=
  CNF.rup_sound cl_27128 [cl_5205,cl_27080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5205 v h) (hints_cons _ _ _ (der_27080 v h) (by intro d hd; cases hd)))
def cl_27129 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,false),(82,false),(88,true)]
theorem der_27129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27129 :=
  CNF.rup_sound cl_27129 [cl_5207,cl_27117] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5207 v h) (hints_cons _ _ _ (der_27117 v h) (by intro d hd; cases hd)))
def cl_27130 : CNF.NClause := [(40,false),(9,true),(63,true),(75,false),(81,true),(82,false),(88,true)]
theorem der_27130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27130 :=
  CNF.rup_sound cl_27130 [cl_5208,cl_27127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5208 v h) (hints_cons _ _ _ (der_27127 v h) (by intro d hd; cases hd)))
def cl_27131 : CNF.NClause := [(40,false),(81,true),(9,false),(63,false),(69,false),(75,true),(82,false)]
theorem der_27131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27131 :=
  CNF.rup_sound cl_27131 [cl_5209,cl_27083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5209 v h) (hints_cons _ _ _ (der_27083 v h) (by intro d hd; cases hd)))
def cl_27132 : CNF.NClause := [(40,false),(81,true),(9,false),(69,false),(75,true),(82,false),(88,true)]
theorem der_27132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27132 :=
  CNF.rup_sound cl_27132 [cl_5211,cl_27131] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5211 v h) (hints_cons _ _ _ (der_27131 v h) (by intro d hd; cases hd)))
def cl_27133 : CNF.NClause := [(40,false),(81,true),(9,true),(63,true),(69,false),(82,false),(88,true)]
theorem der_27133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27133 :=
  CNF.rup_sound cl_27133 [cl_5212,cl_27127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5212 v h) (hints_cons _ _ _ (der_27127 v h) (by intro d hd; cases hd)))
def cl_27134 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,true),(81,true),(82,false)]
theorem der_27134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27134 :=
  CNF.rup_sound cl_27134 [cl_5213,cl_27087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5213 v h) (hints_cons _ _ _ (der_27087 v h) (by intro d hd; cases hd)))
def cl_27135 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,true),(81,true),(82,false)]
theorem der_27135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27135 :=
  CNF.rup_sound cl_27135 [cl_5215,cl_27087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5215 v h) (hints_cons _ _ _ (der_27087 v h) (by intro d hd; cases hd)))
def cl_27136 : CNF.NClause := [(40,false),(69,true),(63,true),(75,true),(81,true),(82,false),(88,true)]
theorem der_27136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27136 :=
  CNF.rup_sound cl_27136 [cl_5216,cl_27135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5216 v h) (hints_cons _ _ _ (der_27135 v h) (by intro d hd; cases hd)))
def cl_27137 : CNF.NClause := [(40,false),(82,true),(9,false),(63,false),(75,false),(69,false),(81,false)]
theorem der_27137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27137 :=
  CNF.rup_sound cl_27137 [cl_5217,cl_5153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5217 v h) (hints_cons _ _ _ (inp_5153 v h) (by intro d hd; cases hd)))
def cl_27138 : CNF.NClause := [(40,false),(82,true),(69,false),(75,false),(81,false),(88,true),(63,false)]
theorem der_27138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27138 :=
  CNF.rup_sound cl_27138 [cl_5218,cl_27137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5218 v h) (hints_cons _ _ _ (der_27137 v h) (by intro d hd; cases hd)))
def cl_27139 : CNF.NClause := [(40,false),(82,true),(9,false),(69,false),(75,false),(81,false),(88,true)]
theorem der_27139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27139 :=
  CNF.rup_sound cl_27139 [cl_5219,cl_27137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5219 v h) (hints_cons _ _ _ (der_27137 v h) (by intro d hd; cases hd)))
def cl_27140 : CNF.NClause := [(40,false),(88,true),(9,true),(63,true),(69,false),(75,false),(81,false)]
theorem der_27140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27140 :=
  CNF.rup_sound cl_27140 [cl_5220,cl_27115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5220 v h) (hints_cons _ _ _ (der_27115 v h) (by intro d hd; cases hd)))
def cl_27141 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,false),(81,false),(82,true)]
theorem der_27141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27141 :=
  CNF.rup_sound cl_27141 [cl_5221,cl_27093] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5221 v h) (hints_cons _ _ _ (der_27093 v h) (by intro d hd; cases hd)))
def cl_27142 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,false),(81,false),(82,true)]
theorem der_27142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27142 :=
  CNF.rup_sound cl_27142 [cl_5223,cl_27099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5223 v h) (hints_cons _ _ _ (der_27099 v h) (by intro d hd; cases hd)))
def cl_27143 : CNF.NClause := [(40,false),(69,true),(9,true),(63,true),(75,false),(81,false),(82,true)]
theorem der_27143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27143 :=
  CNF.rup_sound cl_27143 [cl_5224,cl_27094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5224 v h) (hints_cons _ _ _ (der_27094 v h) (by intro d hd; cases hd)))
def cl_27144 : CNF.NClause := [(40,false),(82,true),(9,false),(63,false),(69,false),(81,false),(88,true)]
theorem der_27144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27144 :=
  CNF.rup_sound cl_27144 [cl_5225,cl_27137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5225 v h) (hints_cons _ _ _ (der_27137 v h) (by intro d hd; cases hd)))
def cl_27145 : CNF.NClause := [(40,false),(82,true),(9,false),(69,false),(81,false),(63,true),(88,true)]
theorem der_27145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27145 :=
  CNF.rup_sound cl_27145 [cl_5227,cl_27139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5227 v h) (hints_cons _ _ _ (der_27139 v h) (by intro d hd; cases hd)))
def cl_27146 : CNF.NClause := [(40,false),(82,true),(63,true),(69,false),(81,false),(75,true),(88,true)]
theorem der_27146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27146 :=
  CNF.rup_sound cl_27146 [cl_5228,cl_27145] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5228 v h) (hints_cons _ _ _ (der_27145 v h) (by intro d hd; cases hd)))
def cl_27147 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(81,false),(82,true),(88,true)]
theorem der_27147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27147 :=
  CNF.rup_sound cl_27147 [cl_5229,cl_27141] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5229 v h) (hints_cons _ _ _ (der_27141 v h) (by intro d hd; cases hd)))
def cl_27148 : CNF.NClause := [(40,false),(69,true),(9,false),(63,true),(75,true),(81,false),(82,true)]
theorem der_27148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27148 :=
  CNF.rup_sound cl_27148 [cl_5231,cl_27099] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5231 v h) (hints_cons _ _ _ (der_27099 v h) (by intro d hd; cases hd)))
def cl_27149 : CNF.NClause := [(40,false),(69,true),(9,true),(63,true),(81,false),(82,true),(88,true)]
theorem der_27149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27149 :=
  CNF.rup_sound cl_27149 [cl_5232,cl_27143] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5232 v h) (hints_cons _ _ _ (der_27143 v h) (by intro d hd; cases hd)))
def cl_27150 : CNF.NClause := [(40,false),(82,true),(9,false),(63,false),(75,false),(69,false),(88,true)]
theorem der_27150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27150 :=
  CNF.rup_sound cl_27150 [cl_5233,cl_27137] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5233 v h) (hints_cons _ _ _ (der_27137 v h) (by intro d hd; cases hd)))
def cl_27152 : CNF.NClause := [(40,false),(9,true),(63,true),(69,false),(75,false),(81,true),(88,true)]
theorem der_27152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27152 :=
  CNF.rup_sound cl_27152 [cl_5236,cl_27127] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5236 v h) (hints_cons _ _ _ (der_27127 v h) (by intro d hd; cases hd)))
def cl_27153 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,false),(81,true),(88,true)]
theorem der_27153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27153 :=
  CNF.rup_sound cl_27153 [cl_5237,cl_27128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5237 v h) (hints_cons _ _ _ (der_27128 v h) (by intro d hd; cases hd)))
def cl_27155 : CNF.NClause := [(40,false),(69,true),(9,true),(63,true),(75,false),(81,true),(82,true)]
theorem der_27155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27155 :=
  CNF.rup_sound cl_27155 [cl_5240,cl_27106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5240 v h) (hints_cons _ _ _ (der_27106 v h) (by intro d hd; cases hd)))
def cl_27158 : CNF.NClause := [(40,false),(81,true),(9,true),(69,false),(75,true),(82,true),(88,true)]
theorem der_27158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27158 :=
  CNF.rup_sound cl_27158 [cl_5244,cl_26807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5244 v h) (hints_cons _ _ _ (der_26807 v h) (by intro d hd; cases hd)))
def cl_27159 : CNF.NClause := [(40,false),(69,true),(63,false),(75,true),(81,true),(82,true),(88,true)]
theorem der_27159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27159 :=
  CNF.rup_sound cl_27159 [cl_5245,cl_26808] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5245 v h) (hints_cons _ _ _ (der_26808 v h) (by intro d hd; cases hd)))
def cl_27161 : CNF.NClause := [(40,false),(69,true),(9,true),(63,true),(81,true),(82,true),(88,true)]
theorem der_27161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27161 :=
  CNF.rup_sound cl_27161 [cl_5248,cl_27155] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5248 v h) (hints_cons _ _ _ (der_27155 v h) (by intro d hd; cases hd)))
def cl_27162 : CNF.NClause := [(60,false),(62,true),(74,false),(68,false),(80,false),(88,false),(86,false)]
theorem der_27162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27162 :=
  CNF.rup_sound cl_27162 [cl_7684,cl_7683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7684 v h) (hints_cons _ _ _ (inp_7683 v h) (by intro d hd; cases hd)))
def cl_27163 : CNF.NClause := [(60,false),(29,true),(62,false),(86,false),(80,false),(74,false),(88,false)]
theorem der_27163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27163 :=
  CNF.rup_sound cl_27163 [cl_7686,cl_7682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7686 v h) (hints_cons _ _ _ (inp_7682 v h) (by intro d hd; cases hd)))
def cl_27164 : CNF.NClause := [(60,false),(29,false),(88,false),(62,true),(86,false),(74,false),(80,false)]
theorem der_27164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27164 :=
  CNF.rup_sound cl_27164 [cl_7687,cl_7683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7687 v h) (hints_cons _ _ _ (inp_7683 v h) (by intro d hd; cases hd)))
def cl_27165 : CNF.NClause := [(60,false),(29,true),(62,true),(88,false),(80,false),(86,false),(74,false)]
theorem der_27165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27165 :=
  CNF.rup_sound cl_27165 [cl_7688,cl_27162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7688 v h) (hints_cons _ _ _ (der_27162 v h) (by intro d hd; cases hd)))
def cl_27166 : CNF.NClause := [(60,false),(74,true),(80,false),(88,false),(86,false),(62,false),(68,false)]
theorem der_27166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27166 :=
  CNF.rup_sound cl_27166 [cl_7690,cl_7689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7690 v h) (hints_cons _ _ _ (inp_7689 v h) (by intro d hd; cases hd)))
def cl_27167 : CNF.NClause := [(60,false),(74,true),(29,false),(68,false),(80,false),(86,false),(88,false)]
theorem der_27167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27167 :=
  CNF.rup_sound cl_27167 [cl_7691,cl_7689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7691 v h) (hints_cons _ _ _ (inp_7689 v h) (by intro d hd; cases hd)))
def cl_27168 : CNF.NClause := [(60,false),(74,true),(62,true),(68,false),(86,false),(80,false),(88,false)]
theorem der_27168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27168 :=
  CNF.rup_sound cl_27168 [cl_7692,cl_27167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7692 v h) (hints_cons _ _ _ (der_27167 v h) (by intro d hd; cases hd)))
def cl_27169 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(80,false),(86,false),(88,false)]
theorem der_27169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27169 :=
  CNF.rup_sound cl_27169 [cl_7693,cl_7689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7693 v h) (hints_cons _ _ _ (inp_7689 v h) (by intro d hd; cases hd)))
def cl_27170 : CNF.NClause := [(60,false),(74,true),(62,false),(68,true),(80,false),(86,false),(88,false)]
theorem der_27170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27170 :=
  CNF.rup_sound cl_27170 [cl_7694,cl_27169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7694 v h) (hints_cons _ _ _ (der_27169 v h) (by intro d hd; cases hd)))
def cl_27171 : CNF.NClause := [(60,false),(74,true),(29,false),(62,true),(80,false),(86,false),(88,false)]
theorem der_27171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27171 :=
  CNF.rup_sound cl_27171 [cl_7695,cl_27167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7695 v h) (hints_cons _ _ _ (der_27167 v h) (by intro d hd; cases hd)))
def cl_27172 : CNF.NClause := [(60,false),(74,true),(62,true),(68,true),(80,false),(86,false),(88,false)]
theorem der_27172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27172 :=
  CNF.rup_sound cl_27172 [cl_7696,cl_27171] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7696 v h) (hints_cons _ _ _ (der_27171 v h) (by intro d hd; cases hd)))
def cl_27173 : CNF.NClause := [(60,false),(29,true),(88,false),(74,false),(86,false),(62,false),(68,false)]
theorem der_27173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27173 :=
  CNF.rup_sound cl_27173 [cl_7698,cl_7682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7698 v h) (hints_cons _ _ _ (inp_7682 v h) (by intro d hd; cases hd)))
def cl_27174 : CNF.NClause := [(60,false),(29,false),(62,true),(88,false),(74,false),(86,false),(68,false)]
theorem der_27174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27174 :=
  CNF.rup_sound cl_27174 [cl_7699,cl_27162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7699 v h) (hints_cons _ _ _ (der_27162 v h) (by intro d hd; cases hd)))
def cl_27175 : CNF.NClause := [(60,false),(29,true),(74,false),(62,true),(68,false),(86,false),(88,false)]
theorem der_27175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27175 :=
  CNF.rup_sound cl_27175 [cl_7700,cl_27162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7700 v h) (hints_cons _ _ _ (der_27162 v h) (by intro d hd; cases hd)))
def cl_27176 : CNF.NClause := [(60,false),(68,true),(29,false),(62,false),(74,false),(86,false),(88,false)]
theorem der_27176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27176 :=
  CNF.rup_sound cl_27176 [cl_7701,cl_7685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7701 v h) (hints_cons _ _ _ (inp_7685 v h) (by intro d hd; cases hd)))
def cl_27177 : CNF.NClause := [(60,false),(68,true),(62,false),(80,true),(74,false),(86,false),(88,false)]
theorem der_27177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27177 :=
  CNF.rup_sound cl_27177 [cl_7702,cl_27176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7702 v h) (hints_cons _ _ _ (der_27176 v h) (by intro d hd; cases hd)))
def cl_27178 : CNF.NClause := [(60,false),(80,true),(29,false),(68,true),(74,false),(86,false),(88,false)]
theorem der_27178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27178 :=
  CNF.rup_sound cl_27178 [cl_7703,cl_27176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7703 v h) (hints_cons _ _ _ (der_27176 v h) (by intro d hd; cases hd)))
def cl_27179 : CNF.NClause := [(60,false),(68,true),(29,true),(62,true),(88,false),(74,false),(86,false)]
theorem der_27179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27179 :=
  CNF.rup_sound cl_27179 [cl_7704,cl_27165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7704 v h) (hints_cons _ _ _ (der_27165 v h) (by intro d hd; cases hd)))
def cl_27180 : CNF.NClause := [(60,false),(74,true),(29,false),(88,false),(86,false),(68,false),(62,false)]
theorem der_27180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27180 :=
  CNF.rup_sound cl_27180 [cl_7705,cl_7689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7705 v h) (hints_cons _ _ _ (inp_7689 v h) (by intro d hd; cases hd)))
def cl_27181 : CNF.NClause := [(60,false),(74,true),(86,false),(62,false),(68,false),(88,false),(80,true)]
theorem der_27181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27181 :=
  CNF.rup_sound cl_27181 [cl_7706,cl_27180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7706 v h) (hints_cons _ _ _ (der_27180 v h) (by intro d hd; cases hd)))
def cl_27182 : CNF.NClause := [(60,false),(74,true),(29,false),(86,false),(88,false),(62,true),(68,false)]
theorem der_27182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27182 :=
  CNF.rup_sound cl_27182 [cl_7707,cl_27167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7707 v h) (hints_cons _ _ _ (der_27167 v h) (by intro d hd; cases hd)))
def cl_27183 : CNF.NClause := [(60,false),(74,true),(86,false),(88,false),(62,true),(68,false),(80,true)]
theorem der_27183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27183 :=
  CNF.rup_sound cl_27183 [cl_7708,cl_27182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7708 v h) (hints_cons _ _ _ (der_27182 v h) (by intro d hd; cases hd)))
def cl_27185 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(86,false),(88,false)]
theorem der_27185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27185 :=
  CNF.rup_sound cl_27185 [cl_7710,cl_27170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7710 v h) (hints_cons _ _ _ (der_27170 v h) (by intro d hd; cases hd)))
def cl_27186 : CNF.NClause := [(60,false),(74,true),(29,false),(62,true),(80,true),(86,false),(88,false)]
theorem der_27186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27186 :=
  CNF.rup_sound cl_27186 [cl_7711,cl_27182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7711 v h) (hints_cons _ _ _ (der_27182 v h) (by intro d hd; cases hd)))
def cl_27187 : CNF.NClause := [(60,false),(74,true),(62,true),(68,true),(80,true),(86,false),(88,false)]
theorem der_27187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27187 :=
  CNF.rup_sound cl_27187 [cl_7712,cl_27186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7712 v h) (hints_cons _ _ _ (der_27186 v h) (by intro d hd; cases hd)))
def cl_27188 : CNF.NClause := [(60,false),(68,false),(29,true),(62,false),(74,false),(80,false),(88,false)]
theorem der_27188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27188 :=
  CNF.rup_sound cl_27188 [cl_7714,cl_27173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7714 v h) (hints_cons _ _ _ (der_27173 v h) (by intro d hd; cases hd)))
def cl_27189 : CNF.NClause := [(60,false),(68,false),(29,false),(62,true),(74,false),(80,false),(88,false)]
theorem der_27189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27189 :=
  CNF.rup_sound cl_27189 [cl_7715,cl_7683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7715 v h) (hints_cons _ _ _ (inp_7683 v h) (by intro d hd; cases hd)))
def cl_27190 : CNF.NClause := [(60,false),(62,true),(29,true),(68,false),(74,false),(80,false),(88,false)]
theorem der_27190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27190 :=
  CNF.rup_sound cl_27190 [cl_7716,cl_27165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7716 v h) (hints_cons _ _ _ (der_27165 v h) (by intro d hd; cases hd)))
def cl_27191 : CNF.NClause := [(60,false),(29,false),(62,false),(74,false),(68,true),(80,false),(88,false)]
theorem der_27191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27191 :=
  CNF.rup_sound cl_27191 [cl_7717,cl_27176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7717 v h) (hints_cons _ _ _ (der_27176 v h) (by intro d hd; cases hd)))
def cl_27192 : CNF.NClause := [(60,false),(29,true),(86,true),(74,false),(62,false),(80,false),(88,false)]
theorem der_27192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27192 :=
  CNF.rup_sound cl_27192 [cl_7718,cl_27188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7718 v h) (hints_cons _ _ _ (der_27188 v h) (by intro d hd; cases hd)))
def cl_27193 : CNF.NClause := [(60,false),(68,true),(29,false),(62,true),(74,false),(80,false),(88,false)]
theorem der_27193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27193 :=
  CNF.rup_sound cl_27193 [cl_7719,cl_27164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7719 v h) (hints_cons _ _ _ (der_27164 v h) (by intro d hd; cases hd)))
def cl_27194 : CNF.NClause := [(60,false),(68,true),(86,true),(62,true),(80,false),(74,false),(88,false)]
theorem der_27194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27194 :=
  CNF.rup_sound cl_27194 [cl_7720,cl_27193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7720 v h) (hints_cons _ _ _ (der_27193 v h) (by intro d hd; cases hd)))
def cl_27195 : CNF.NClause := [(60,false),(74,true),(29,false),(80,false),(62,false),(88,false),(68,false)]
theorem der_27195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27195 :=
  CNF.rup_sound cl_27195 [cl_7721,cl_7689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7721 v h) (hints_cons _ _ _ (inp_7689 v h) (by intro d hd; cases hd)))
def cl_27196 : CNF.NClause := [(60,false),(29,true),(68,false),(86,true),(80,false),(62,false),(88,false)]
theorem der_27196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27196 :=
  CNF.rup_sound cl_27196 [cl_7722,cl_27188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7722 v h) (hints_cons _ _ _ (der_27188 v h) (by intro d hd; cases hd)))
def cl_27197 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(80,false),(74,true),(88,false)]
theorem der_27197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27197 :=
  CNF.rup_sound cl_27197 [cl_7723,cl_27182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7723 v h) (hints_cons _ _ _ (der_27182 v h) (by intro d hd; cases hd)))
def cl_27198 : CNF.NClause := [(60,false),(88,false),(68,false),(74,true),(80,false),(62,true),(86,true)]
theorem der_27198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27198 :=
  CNF.rup_sound cl_27198 [cl_7724,cl_27197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7724 v h) (hints_cons _ _ _ (der_27197 v h) (by intro d hd; cases hd)))
def cl_27199 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(68,true),(80,false),(88,false)]
theorem der_27199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27199 :=
  CNF.rup_sound cl_27199 [cl_7725,cl_27169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7725 v h) (hints_cons _ _ _ (der_27169 v h) (by intro d hd; cases hd)))
def cl_27200 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(80,false),(88,false)]
theorem der_27200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27200 :=
  CNF.rup_sound cl_27200 [cl_7726,cl_27185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7726 v h) (hints_cons _ _ _ (der_27185 v h) (by intro d hd; cases hd)))
def cl_27201 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(80,false),(86,true),(88,false)]
theorem der_27201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27201 :=
  CNF.rup_sound cl_27201 [cl_7727,cl_27193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7727 v h) (hints_cons _ _ _ (der_27193 v h) (by intro d hd; cases hd)))
def cl_27202 : CNF.NClause := [(60,false),(74,true),(29,true),(68,true),(80,false),(86,true),(88,false)]
theorem der_27202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27202 :=
  CNF.rup_sound cl_27202 [cl_7728,cl_27200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7728 v h) (hints_cons _ _ _ (der_27200 v h) (by intro d hd; cases hd)))
def cl_27203 : CNF.NClause := [(60,false),(86,true),(29,false),(68,false),(74,false),(62,false),(88,false)]
theorem der_27203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27203 :=
  CNF.rup_sound cl_27203 [cl_7729,cl_7713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7729 v h) (hints_cons _ _ _ (inp_7713 v h) (by intro d hd; cases hd)))
def cl_27204 : CNF.NClause := [(60,false),(80,true),(29,true),(74,false),(68,false),(62,false),(88,false)]
theorem der_27204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27204 :=
  CNF.rup_sound cl_27204 [cl_7730,cl_27173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7730 v h) (hints_cons _ _ _ (der_27173 v h) (by intro d hd; cases hd)))
def cl_27205 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(88,false)]
theorem der_27205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27205 :=
  CNF.rup_sound cl_27205 [cl_7731,cl_27174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7731 v h) (hints_cons _ _ _ (der_27174 v h) (by intro d hd; cases hd)))
def cl_27206 : CNF.NClause := [(60,false),(80,true),(29,true),(68,false),(74,false),(88,false),(86,true)]
theorem der_27206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27206 :=
  CNF.rup_sound cl_27206 [cl_7732,cl_27204] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7732 v h) (hints_cons _ _ _ (der_27204 v h) (by intro d hd; cases hd)))
def cl_27207 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,false),(80,true),(88,false)]
theorem der_27207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27207 :=
  CNF.rup_sound cl_27207 [cl_7733,cl_27176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7733 v h) (hints_cons _ _ _ (der_27176 v h) (by intro d hd; cases hd)))
def cl_27208 : CNF.NClause := [(60,false),(86,true),(29,true),(62,false),(68,true),(74,false),(88,false)]
theorem der_27208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27208 :=
  CNF.rup_sound cl_27208 [cl_7734,cl_27192] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7734 v h) (hints_cons _ _ _ (der_27192 v h) (by intro d hd; cases hd)))
def cl_27209 : CNF.NClause := [(60,false),(86,true),(29,false),(62,true),(68,true),(74,false),(88,false)]
theorem der_27209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27209 :=
  CNF.rup_sound cl_27209 [cl_7735,cl_27193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7735 v h) (hints_cons _ _ _ (der_27193 v h) (by intro d hd; cases hd)))
def cl_27210 : CNF.NClause := [(60,false),(86,true),(62,true),(68,true),(74,false),(80,true),(88,false)]
theorem der_27210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27210 :=
  CNF.rup_sound cl_27210 [cl_7736,cl_27209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7736 v h) (hints_cons _ _ _ (der_27209 v h) (by intro d hd; cases hd)))
def cl_27211 : CNF.NClause := [(60,false),(74,true),(29,false),(88,false),(80,true),(62,false),(68,false)]
theorem der_27211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27211 :=
  CNF.rup_sound cl_27211 [cl_7737,cl_27180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7737 v h) (hints_cons _ _ _ (der_27180 v h) (by intro d hd; cases hd)))
def cl_27212 : CNF.NClause := [(60,false),(74,true),(86,true),(68,false),(80,true),(62,false),(88,false)]
theorem der_27212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27212 :=
  CNF.rup_sound cl_27212 [cl_7738,cl_27211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7738 v h) (hints_cons _ _ _ (der_27211 v h) (by intro d hd; cases hd)))
def cl_27213 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(80,true),(74,true),(88,false)]
theorem der_27213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27213 :=
  CNF.rup_sound cl_27213 [cl_7739,cl_27182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7739 v h) (hints_cons _ _ _ (der_27182 v h) (by intro d hd; cases hd)))
def cl_27214 : CNF.NClause := [(60,false),(88,false),(29,true),(68,false),(74,true),(62,true),(86,true)]
theorem der_27214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27214 :=
  CNF.rup_sound cl_27214 [cl_7740,cl_27198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7740 v h) (hints_cons _ _ _ (der_27198 v h) (by intro d hd; cases hd)))
def cl_27215 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(80,true),(86,true),(88,false)]
theorem der_27215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27215 :=
  CNF.rup_sound cl_27215 [cl_7741,cl_27211] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7741 v h) (hints_cons _ _ _ (der_27211 v h) (by intro d hd; cases hd)))
def cl_27216 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(86,true),(88,false)]
theorem der_27216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27216 :=
  CNF.rup_sound cl_27216 [cl_7742,cl_27200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7742 v h) (hints_cons _ _ _ (der_27200 v h) (by intro d hd; cases hd)))
def cl_27217 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(80,true),(86,true),(88,false)]
theorem der_27217 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27217 :=
  CNF.rup_sound cl_27217 [cl_7743,cl_27209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7743 v h) (hints_cons _ _ _ (der_27209 v h) (by intro d hd; cases hd)))
def cl_27218 : CNF.NClause := [(60,false),(74,true),(29,true),(62,true),(68,true),(86,true),(88,false)]
theorem der_27218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27218 :=
  CNF.rup_sound cl_27218 [cl_7744,cl_27202] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7744 v h) (hints_cons _ _ _ (der_27202 v h) (by intro d hd; cases hd)))
def cl_27219 : CNF.NClause := [(60,false),(29,true),(86,false),(74,false),(68,false),(62,false),(80,false)]
theorem der_27219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27219 :=
  CNF.rup_sound cl_27219 [cl_7746,cl_27173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7746 v h) (hints_cons _ _ _ (der_27173 v h) (by intro d hd; cases hd)))
def cl_27220 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,false)]
theorem der_27220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27220 :=
  CNF.rup_sound cl_27220 [cl_7747,cl_27174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7747 v h) (hints_cons _ _ _ (der_27174 v h) (by intro d hd; cases hd)))
def cl_27221 : CNF.NClause := [(60,false),(29,true),(68,false),(74,false),(80,false),(62,true),(86,false)]
theorem der_27221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27221 :=
  CNF.rup_sound cl_27221 [cl_7748,cl_27165] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7748 v h) (hints_cons _ _ _ (der_27165 v h) (by intro d hd; cases hd)))
def cl_27222 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(80,false),(86,false),(74,false)]
theorem der_27222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27222 :=
  CNF.rup_sound cl_27222 [cl_7749,cl_27176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7749 v h) (hints_cons _ _ _ (der_27176 v h) (by intro d hd; cases hd)))
def cl_27223 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(80,false),(74,false),(86,false)]
theorem der_27223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27223 :=
  CNF.rup_sound cl_27223 [cl_7750,cl_27163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7750 v h) (hints_cons _ _ _ (der_27163 v h) (by intro d hd; cases hd)))
def cl_27224 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(80,false),(74,false),(86,false)]
theorem der_27224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27224 :=
  CNF.rup_sound cl_27224 [cl_7751,cl_27193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7751 v h) (hints_cons _ _ _ (der_27193 v h) (by intro d hd; cases hd)))
def cl_27225 : CNF.NClause := [(60,false),(88,true),(86,false),(62,true),(68,true),(74,false),(80,false)]
theorem der_27225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27225 :=
  CNF.rup_sound cl_27225 [cl_7752,cl_27224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7752 v h) (hints_cons _ _ _ (der_27224 v h) (by intro d hd; cases hd)))
def cl_27226 : CNF.NClause := [(60,false),(29,false),(68,false),(74,true),(80,false),(62,false),(86,false)]
theorem der_27226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27226 :=
  CNF.rup_sound cl_27226 [cl_7753,cl_7689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7753 v h) (hints_cons _ _ _ (inp_7689 v h) (by intro d hd; cases hd)))
def cl_27227 : CNF.NClause := [(60,false),(88,true),(68,false),(74,true),(80,false),(62,false),(86,false)]
theorem der_27227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27227 :=
  CNF.rup_sound cl_27227 [cl_7754,cl_27226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7754 v h) (hints_cons _ _ _ (der_27226 v h) (by intro d hd; cases hd)))
def cl_27228 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(80,false),(86,false),(74,true)]
theorem der_27228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27228 :=
  CNF.rup_sound cl_27228 [cl_7755,cl_27182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7755 v h) (hints_cons _ _ _ (der_27182 v h) (by intro d hd; cases hd)))
def cl_27229 : CNF.NClause := [(60,false),(88,true),(74,true),(68,false),(80,false),(86,false),(62,true)]
theorem der_27229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27229 :=
  CNF.rup_sound cl_27229 [cl_7756,cl_27228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7756 v h) (hints_cons _ _ _ (der_27228 v h) (by intro d hd; cases hd)))
def cl_27230 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(68,true),(80,false),(86,false)]
theorem der_27230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27230 :=
  CNF.rup_sound cl_27230 [cl_7757,cl_27169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7757 v h) (hints_cons _ _ _ (der_27169 v h) (by intro d hd; cases hd)))
def cl_27231 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(80,false),(86,false)]
theorem der_27231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27231 :=
  CNF.rup_sound cl_27231 [cl_7758,cl_27200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7758 v h) (hints_cons _ _ _ (der_27200 v h) (by intro d hd; cases hd)))
def cl_27232 : CNF.NClause := [(60,false),(74,true),(29,false),(62,true),(80,false),(86,false),(88,true)]
theorem der_27232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27232 :=
  CNF.rup_sound cl_27232 [cl_7759,cl_27228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7759 v h) (hints_cons _ _ _ (der_27228 v h) (by intro d hd; cases hd)))
def cl_27233 : CNF.NClause := [(60,false),(74,true),(62,true),(68,true),(80,false),(86,false),(88,true)]
theorem der_27233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27233 :=
  CNF.rup_sound cl_27233 [cl_7760,cl_27232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7760 v h) (hints_cons _ _ _ (der_27232 v h) (by intro d hd; cases hd)))
def cl_27234 : CNF.NClause := [(60,false),(88,true),(29,false),(68,false),(74,false),(62,false),(86,false)]
theorem der_27234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27234 :=
  CNF.rup_sound cl_27234 [cl_7761,cl_7745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7761 v h) (hints_cons _ _ _ (inp_7745 v h) (by intro d hd; cases hd)))
def cl_27235 : CNF.NClause := [(60,false),(29,true),(68,false),(74,false),(80,true),(62,false),(86,false)]
theorem der_27235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27235 :=
  CNF.rup_sound cl_27235 [cl_7762,cl_27173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7762 v h) (hints_cons _ _ _ (der_27173 v h) (by intro d hd; cases hd)))
def cl_27236 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(86,false),(80,true)]
theorem der_27236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27236 :=
  CNF.rup_sound cl_27236 [cl_7763,cl_27174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7763 v h) (hints_cons _ _ _ (der_27174 v h) (by intro d hd; cases hd)))
def cl_27237 : CNF.NClause := [(60,false),(29,true),(80,true),(74,false),(68,false),(86,false),(62,true)]
theorem der_27237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27237 :=
  CNF.rup_sound cl_27237 [cl_7764,cl_27175] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7764 v h) (hints_cons _ _ _ (der_27175 v h) (by intro d hd; cases hd)))
def cl_27238 : CNF.NClause := [(60,false),(68,true),(29,false),(62,false),(80,true),(74,false),(86,false)]
theorem der_27238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27238 :=
  CNF.rup_sound cl_27238 [cl_7765,cl_27176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7765 v h) (hints_cons _ _ _ (der_27176 v h) (by intro d hd; cases hd)))
def cl_27239 : CNF.NClause := [(60,false),(68,true),(62,false),(80,true),(74,false),(86,false),(88,true)]
theorem der_27239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27239 :=
  CNF.rup_sound cl_27239 [cl_7766,cl_27238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7766 v h) (hints_cons _ _ _ (der_27238 v h) (by intro d hd; cases hd)))
def cl_27240 : CNF.NClause := [(60,false),(88,true),(29,false),(62,true),(68,true),(74,false),(86,false)]
theorem der_27240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27240 :=
  CNF.rup_sound cl_27240 [cl_7767,cl_27224] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7767 v h) (hints_cons _ _ _ (der_27224 v h) (by intro d hd; cases hd)))
def cl_27241 : CNF.NClause := [(60,false),(29,true),(88,true),(62,true),(74,false),(80,true),(86,false)]
theorem der_27241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27241 :=
  CNF.rup_sound cl_27241 [cl_7768,cl_27237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7768 v h) (hints_cons _ _ _ (der_27237 v h) (by intro d hd; cases hd)))
def cl_27242 : CNF.NClause := [(60,false),(29,false),(68,false),(74,true),(80,true),(62,false),(86,false)]
theorem der_27242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27242 :=
  CNF.rup_sound cl_27242 [cl_7769,cl_27180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7769 v h) (hints_cons _ _ _ (der_27180 v h) (by intro d hd; cases hd)))
def cl_27243 : CNF.NClause := [(60,false),(88,true),(68,false),(74,true),(80,true),(62,false),(86,false)]
theorem der_27243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27243 :=
  CNF.rup_sound cl_27243 [cl_7770,cl_27242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7770 v h) (hints_cons _ _ _ (der_27242 v h) (by intro d hd; cases hd)))
def cl_27244 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(80,true),(74,true),(86,false)]
theorem der_27244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27244 :=
  CNF.rup_sound cl_27244 [cl_7771,cl_27182] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7771 v h) (hints_cons _ _ _ (der_27182 v h) (by intro d hd; cases hd)))
def cl_27245 : CNF.NClause := [(60,false),(88,true),(29,true),(62,true),(68,false),(80,true),(86,false)]
theorem der_27245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27245 :=
  CNF.rup_sound cl_27245 [cl_7772,cl_27237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7772 v h) (hints_cons _ _ _ (der_27237 v h) (by intro d hd; cases hd)))
def cl_27246 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(80,true),(86,false),(88,true)]
theorem der_27246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27246 :=
  CNF.rup_sound cl_27246 [cl_7773,cl_27242] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7773 v h) (hints_cons _ _ _ (der_27242 v h) (by intro d hd; cases hd)))
def cl_27247 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(80,true),(86,false)]
theorem der_27247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27247 :=
  CNF.rup_sound cl_27247 [cl_7774,cl_27185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7774 v h) (hints_cons _ _ _ (der_27185 v h) (by intro d hd; cases hd)))
def cl_27249 : CNF.NClause := [(60,false),(74,true),(29,true),(68,true),(80,true),(86,false),(88,true)]
theorem der_27249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27249 :=
  CNF.rup_sound cl_27249 [cl_7776,cl_27247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7776 v h) (hints_cons _ _ _ (der_27247 v h) (by intro d hd; cases hd)))
def cl_27250 : CNF.NClause := [(60,false),(29,false),(68,false),(74,false),(80,false),(62,false),(86,true)]
theorem der_27250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27250 :=
  CNF.rup_sound cl_27250 [cl_7777,cl_27203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7777 v h) (hints_cons _ _ _ (der_27203 v h) (by intro d hd; cases hd)))
def cl_27251 : CNF.NClause := [(60,false),(29,true),(68,false),(74,false),(80,false),(62,false),(86,true)]
theorem der_27251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27251 :=
  CNF.rup_sound cl_27251 [cl_7778,cl_27188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7778 v h) (hints_cons _ _ _ (der_27188 v h) (by intro d hd; cases hd)))
def cl_27252 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,false),(86,true)]
theorem der_27252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27252 :=
  CNF.rup_sound cl_27252 [cl_7779,cl_27189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7779 v h) (hints_cons _ _ _ (der_27189 v h) (by intro d hd; cases hd)))
def cl_27253 : CNF.NClause := [(60,false),(29,true),(68,false),(74,false),(80,false),(62,true),(86,true)]
theorem der_27253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27253 :=
  CNF.rup_sound cl_27253 [cl_7780,cl_27190] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7780 v h) (hints_cons _ _ _ (der_27190 v h) (by intro d hd; cases hd)))
def cl_27254 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(80,false),(86,true),(74,false)]
theorem der_27254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27254 :=
  CNF.rup_sound cl_27254 [cl_7781,cl_27191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7781 v h) (hints_cons _ _ _ (der_27191 v h) (by intro d hd; cases hd)))
def cl_27255 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(80,false),(86,true),(74,false)]
theorem der_27255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27255 :=
  CNF.rup_sound cl_27255 [cl_7782,cl_27208] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7782 v h) (hints_cons _ _ _ (der_27208 v h) (by intro d hd; cases hd)))
def cl_27256 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(80,false),(86,true),(74,false)]
theorem der_27256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27256 :=
  CNF.rup_sound cl_27256 [cl_7783,cl_27193] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7783 v h) (hints_cons _ _ _ (der_27193 v h) (by intro d hd; cases hd)))
def cl_27257 : CNF.NClause := [(60,false),(88,true),(29,true),(68,true),(80,false),(86,true),(74,false)]
theorem der_27257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27257 :=
  CNF.rup_sound cl_27257 [cl_7784,cl_27255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7784 v h) (hints_cons _ _ _ (der_27255 v h) (by intro d hd; cases hd)))
def cl_27258 : CNF.NClause := [(60,false),(29,false),(68,false),(74,true),(80,false),(62,false),(86,true)]
theorem der_27258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27258 :=
  CNF.rup_sound cl_27258 [cl_7785,cl_27195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7785 v h) (hints_cons _ _ _ (der_27195 v h) (by intro d hd; cases hd)))
def cl_27259 : CNF.NClause := [(60,false),(29,true),(68,false),(74,true),(80,false),(62,false),(86,true)]
theorem der_27259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27259 :=
  CNF.rup_sound cl_27259 [cl_7786,cl_27196] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7786 v h) (hints_cons _ _ _ (der_27196 v h) (by intro d hd; cases hd)))
def cl_27260 : CNF.NClause := [(60,false),(88,true),(29,false),(62,true),(68,false),(80,false),(74,true)]
theorem der_27260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27260 :=
  CNF.rup_sound cl_27260 [cl_7787,cl_27228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7787 v h) (hints_cons _ _ _ (der_27228 v h) (by intro d hd; cases hd)))
def cl_27261 : CNF.NClause := [(60,false),(88,true),(68,false),(74,true),(80,false),(62,true),(86,true)]
theorem der_27261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27261 :=
  CNF.rup_sound cl_27261 [cl_7788,cl_27260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7788 v h) (hints_cons _ _ _ (der_27260 v h) (by intro d hd; cases hd)))
def cl_27262 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(80,false),(86,true),(88,true)]
theorem der_27262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27262 :=
  CNF.rup_sound cl_27262 [cl_7789,cl_27258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7789 v h) (hints_cons _ _ _ (der_27258 v h) (by intro d hd; cases hd)))
def cl_27263 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(80,false),(86,true)]
theorem der_27263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27263 :=
  CNF.rup_sound cl_27263 [cl_7790,cl_27200] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7790 v h) (hints_cons _ _ _ (der_27200 v h) (by intro d hd; cases hd)))
def cl_27264 : CNF.NClause := [(60,false),(74,true),(29,false),(62,true),(80,false),(86,true),(88,true)]
theorem der_27264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27264 :=
  CNF.rup_sound cl_27264 [cl_7791,cl_27260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7791 v h) (hints_cons _ _ _ (der_27260 v h) (by intro d hd; cases hd)))
def cl_27265 : CNF.NClause := [(60,false),(74,true),(62,true),(68,true),(80,false),(86,true),(88,true)]
theorem der_27265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27265 :=
  CNF.rup_sound cl_27265 [cl_7792,cl_27264] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7792 v h) (hints_cons _ _ _ (der_27264 v h) (by intro d hd; cases hd)))
def cl_27266 : CNF.NClause := [(60,false),(29,false),(68,false),(74,false),(62,false),(80,true),(86,true)]
theorem der_27266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27266 :=
  CNF.rup_sound cl_27266 [cl_7793,cl_27203] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7793 v h) (hints_cons _ _ _ (der_27203 v h) (by intro d hd; cases hd)))
def cl_27267 : CNF.NClause := [(60,false),(88,true),(68,false),(74,false),(80,true),(62,false),(86,true)]
theorem der_27267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27267 :=
  CNF.rup_sound cl_27267 [cl_7794,cl_27266] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7794 v h) (hints_cons _ _ _ (der_27266 v h) (by intro d hd; cases hd)))
def cl_27268 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,false),(80,true),(86,true)]
theorem der_27268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27268 :=
  CNF.rup_sound cl_27268 [cl_7795,cl_27205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7795 v h) (hints_cons _ _ _ (der_27205 v h) (by intro d hd; cases hd)))
def cl_27269 : CNF.NClause := [(60,false),(88,true),(29,true),(68,false),(74,false),(80,true),(62,true)]
theorem der_27269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27269 :=
  CNF.rup_sound cl_27269 [cl_7796,cl_27237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7796 v h) (hints_cons _ _ _ (der_27237 v h) (by intro d hd; cases hd)))
def cl_27270 : CNF.NClause := [(60,false),(86,true),(29,false),(62,false),(68,true),(74,false),(88,true)]
theorem der_27270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27270 :=
  CNF.rup_sound cl_27270 [cl_7797,cl_27254] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7797 v h) (hints_cons _ _ _ (der_27254 v h) (by intro d hd; cases hd)))
def cl_27271 : CNF.NClause := [(60,false),(86,true),(62,false),(68,true),(74,false),(80,true),(88,true)]
theorem der_27271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27271 :=
  CNF.rup_sound cl_27271 [cl_7798,cl_27270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7798 v h) (hints_cons _ _ _ (der_27270 v h) (by intro d hd; cases hd)))
def cl_27272 : CNF.NClause := [(60,false),(86,true),(29,false),(62,true),(68,true),(74,false),(80,true)]
theorem der_27272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27272 :=
  CNF.rup_sound cl_27272 [cl_7799,cl_27209] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7799 v h) (hints_cons _ _ _ (der_27209 v h) (by intro d hd; cases hd)))
def cl_27273 : CNF.NClause := [(60,false),(86,true),(29,true),(62,true),(68,true),(74,false),(80,true)]
theorem der_27273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27273 :=
  CNF.rup_sound cl_27273 [cl_7800,cl_27210] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7800 v h) (hints_cons _ _ _ (der_27210 v h) (by intro d hd; cases hd)))
def cl_27274 : CNF.NClause := [(60,false),(29,false),(68,false),(74,true),(80,true),(62,false),(86,true)]
theorem der_27274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27274 :=
  CNF.rup_sound cl_27274 [cl_7801,cl_27215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7801 v h) (hints_cons _ _ _ (der_27215 v h) (by intro d hd; cases hd)))
def cl_27275 : CNF.NClause := [(60,false),(29,true),(68,false),(74,true),(80,true),(62,false),(86,true)]
theorem der_27275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27275 :=
  CNF.rup_sound cl_27275 [cl_7802,cl_27212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7802 v h) (hints_cons _ _ _ (der_27212 v h) (by intro d hd; cases hd)))
def cl_27276 : CNF.NClause := [(60,false),(88,true),(29,false),(62,true),(68,false),(74,true),(86,true)]
theorem der_27276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27276 :=
  CNF.rup_sound cl_27276 [cl_7803,cl_27260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7803 v h) (hints_cons _ _ _ (der_27260 v h) (by intro d hd; cases hd)))
def cl_27277 : CNF.NClause := [(60,false),(88,true),(29,true),(68,false),(74,true),(80,true),(86,true)]
theorem der_27277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27277 :=
  CNF.rup_sound cl_27277 [cl_7804,cl_27275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7804 v h) (hints_cons _ _ _ (der_27275 v h) (by intro d hd; cases hd)))
def cl_27278 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(68,true),(80,true),(86,true)]
theorem der_27278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27278 :=
  CNF.rup_sound cl_27278 [cl_7805,cl_27215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7805 v h) (hints_cons _ _ _ (der_27215 v h) (by intro d hd; cases hd)))
def cl_27279 : CNF.NClause := [(60,false),(74,true),(29,true),(62,false),(68,true),(80,true),(88,true)]
theorem der_27279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27279 :=
  CNF.rup_sound cl_27279 [cl_7806,cl_27247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7806 v h) (hints_cons _ _ _ (der_27247 v h) (by intro d hd; cases hd)))
def cl_27280 : CNF.NClause := [(60,false),(74,true),(29,false),(68,true),(80,true),(86,true),(88,true)]
theorem der_27280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27280 :=
  CNF.rup_sound cl_27280 [cl_7807,cl_27278] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7807 v h) (hints_cons _ _ _ (der_27278 v h) (by intro d hd; cases hd)))
def cl_27281 : CNF.NClause := [(60,false),(74,true),(62,true),(68,true),(80,true),(86,true),(88,true)]
theorem der_27281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27281 :=
  CNF.rup_sound cl_27281 [cl_7808,cl_27280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7808 v h) (hints_cons _ _ _ (der_27280 v h) (by intro d hd; cases hd)))
def cl_27282 : CNF.NClause := [(55,false),(63,true),(76,false),(80,false),(91,false),(84,false),(67,false)]
theorem der_27282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27282 :=
  CNF.rup_sound cl_27282 [cl_7044,cl_7043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7044 v h) (hints_cons _ _ _ (inp_7043 v h) (by intro d hd; cases hd)))
def cl_27283 : CNF.NClause := [(55,false),(67,true),(91,false),(76,false),(63,false),(80,false),(84,false)]
theorem der_27283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27283 :=
  CNF.rup_sound cl_27283 [cl_7046,cl_7045] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7046 v h) (hints_cons _ _ _ (inp_7045 v h) (by intro d hd; cases hd)))
def cl_27284 : CNF.NClause := [(55,false),(80,false),(24,false),(63,true),(76,false),(84,false),(91,false)]
theorem der_27284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27284 :=
  CNF.rup_sound cl_27284 [cl_7047,cl_7043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7047 v h) (hints_cons _ _ _ (inp_7043 v h) (by intro d hd; cases hd)))
def cl_27285 : CNF.NClause := [(55,false),(80,false),(76,false),(67,true),(91,false),(84,false),(63,true)]
theorem der_27285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27285 :=
  CNF.rup_sound cl_27285 [cl_7048,cl_27284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7048 v h) (hints_cons _ _ _ (der_27284 v h) (by intro d hd; cases hd)))
def cl_27286 : CNF.NClause := [(55,false),(67,false),(91,false),(63,false),(76,true),(80,false),(84,false)]
theorem der_27286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27286 :=
  CNF.rup_sound cl_27286 [cl_7050,cl_7049] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7050 v h) (hints_cons _ _ _ (inp_7049 v h) (by intro d hd; cases hd)))
def cl_27287 : CNF.NClause := [(55,false),(24,false),(80,false),(67,false),(76,true),(84,false),(91,false)]
theorem der_27287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27287 :=
  CNF.rup_sound cl_27287 [cl_7051,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7051 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27288 : CNF.NClause := [(55,false),(24,true),(84,false),(80,false),(76,true),(67,false),(91,false)]
theorem der_27288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27288 :=
  CNF.rup_sound cl_27288 [cl_7052,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7052 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27289 : CNF.NClause := [(55,false),(24,false),(63,false),(91,false),(76,true),(84,false),(80,false)]
theorem der_27289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27289 :=
  CNF.rup_sound cl_27289 [cl_7053,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7053 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27290 : CNF.NClause := [(55,false),(24,true),(63,false),(76,true),(84,false),(80,false),(91,false)]
theorem der_27290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27290 :=
  CNF.rup_sound cl_27290 [cl_7054,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7054 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27291 : CNF.NClause := [(55,false),(63,true),(24,false),(67,true),(80,false),(84,false),(91,false)]
theorem der_27291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27291 :=
  CNF.rup_sound cl_27291 [cl_7055,cl_27284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7055 v h) (hints_cons _ _ _ (der_27284 v h) (by intro d hd; cases hd)))
def cl_27292 : CNF.NClause := [(55,false),(24,true),(80,false),(76,true),(63,true),(84,false),(91,false)]
theorem der_27292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27292 :=
  CNF.rup_sound cl_27292 [cl_7056,cl_27288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7056 v h) (hints_cons _ _ _ (der_27288 v h) (by intro d hd; cases hd)))
def cl_27293 : CNF.NClause := [(55,false),(80,true),(63,false),(84,false),(76,false),(91,false),(67,false)]
theorem der_27293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27293 :=
  CNF.rup_sound cl_27293 [cl_7058,cl_7057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7058 v h) (hints_cons _ _ _ (inp_7057 v h) (by intro d hd; cases hd)))
def cl_27294 : CNF.NClause := [(55,false),(80,true),(24,false),(67,false),(76,false),(84,false),(91,false)]
theorem der_27294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27294 :=
  CNF.rup_sound cl_27294 [cl_7059,cl_7057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7059 v h) (hints_cons _ _ _ (inp_7057 v h) (by intro d hd; cases hd)))
def cl_27295 : CNF.NClause := [(55,false),(80,true),(91,false),(76,false),(63,true),(84,false),(67,false)]
theorem der_27295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27295 :=
  CNF.rup_sound cl_27295 [cl_7060,cl_27294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7060 v h) (hints_cons _ _ _ (der_27294 v h) (by intro d hd; cases hd)))
def cl_27296 : CNF.NClause := [(55,false),(80,true),(24,false),(63,false),(91,false),(84,false),(76,false)]
theorem der_27296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27296 :=
  CNF.rup_sound cl_27296 [cl_7061,cl_7057] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7061 v h) (hints_cons _ _ _ (inp_7057 v h) (by intro d hd; cases hd)))
def cl_27297 : CNF.NClause := [(55,false),(80,true),(63,false),(76,false),(67,true),(84,false),(91,false)]
theorem der_27297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27297 :=
  CNF.rup_sound cl_27297 [cl_7062,cl_27296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7062 v h) (hints_cons _ _ _ (der_27296 v h) (by intro d hd; cases hd)))
def cl_27298 : CNF.NClause := [(55,false),(80,true),(24,false),(63,true),(76,false),(84,false),(91,false)]
theorem der_27298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27298 :=
  CNF.rup_sound cl_27298 [cl_7063,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7063 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27299 : CNF.NClause := [(55,false),(80,true),(24,true),(63,true),(76,false),(84,false),(91,false)]
theorem der_27299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27299 :=
  CNF.rup_sound cl_27299 [cl_7064,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7064 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27300 : CNF.NClause := [(55,false),(24,false),(91,false),(63,false),(67,false),(76,true),(84,false)]
theorem der_27300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27300 :=
  CNF.rup_sound cl_27300 [cl_7065,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7065 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27301 : CNF.NClause := [(55,false),(24,true),(67,false),(91,false),(84,false),(63,false),(76,true)]
theorem der_27301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27301 :=
  CNF.rup_sound cl_27301 [cl_7066,cl_27286] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7066 v h) (hints_cons _ _ _ (der_27286 v h) (by intro d hd; cases hd)))
def cl_27302 : CNF.NClause := [(55,false),(80,true),(24,false),(63,true),(67,false),(84,false),(91,false)]
theorem der_27302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27302 :=
  CNF.rup_sound cl_27302 [cl_7067,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7067 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def cl_27303 : CNF.NClause := [(55,false),(80,true),(24,true),(63,true),(67,false),(84,false),(91,false)]
theorem der_27303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27303 :=
  CNF.rup_sound cl_27303 [cl_7068,cl_27295] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7068 v h) (hints_cons _ _ _ (der_27295 v h) (by intro d hd; cases hd)))
def chunk009 : List CNF.NClause := [cl_26787,cl_26788,cl_26789,cl_26790,cl_26791,cl_26792,cl_26793,cl_26794,cl_26795,cl_26796,cl_26797,cl_26798,cl_26799,cl_26800,cl_26801,cl_26802,cl_26803,cl_26804,cl_26805,cl_26806,cl_26807,cl_26808,cl_26809,cl_26810,cl_26811,cl_26812,cl_26813,cl_26814,cl_26815,cl_26816,cl_26817,cl_26818,cl_26819,cl_26820,cl_26821,cl_26822,cl_26823,cl_26824,cl_26825,cl_26826,cl_26827,cl_26828,cl_26829,cl_26830,cl_26831,cl_26832,cl_26833,cl_26834,cl_26835,cl_26836,cl_26837,cl_26838,cl_26839,cl_26840,cl_26841,cl_26842,cl_26843,cl_26844,cl_26845,cl_26846,cl_26847,cl_26848,cl_26849,cl_26850,cl_26851,cl_26852,cl_26853,cl_26854,cl_26855,cl_26856,cl_26857,cl_26858,cl_26859,cl_26860,cl_26861,cl_26862,cl_26863,cl_26864,cl_26865,cl_26866,cl_26867,cl_26868,cl_26869,cl_26870,cl_26871,cl_26872,cl_26873,cl_26874,cl_26875,cl_26876,cl_26877,cl_26878,cl_26879,cl_26880,cl_26881,cl_26883,cl_26884,cl_26885,cl_26886,cl_26887,cl_26888,cl_26889,cl_26890,cl_26891,cl_26892,cl_26893,cl_26894,cl_26895,cl_26896,cl_26897,cl_26898,cl_26899,cl_26900,cl_26901,cl_26902,cl_26903,cl_26904,cl_26905,cl_26906,cl_26907,cl_26908,cl_26909,cl_26910,cl_26911,cl_26912,cl_26914,cl_26915,cl_26916,cl_26917,cl_26918,cl_26919,cl_26920,cl_26921,cl_26922,cl_26923,cl_26924,cl_26925,cl_26926,cl_26927,cl_26928,cl_26929,cl_26930,cl_26931,cl_26932,cl_26933,cl_26934,cl_26935,cl_26936,cl_26937,cl_26938,cl_26939,cl_26940,cl_26942,cl_26943,cl_26944,cl_26946,cl_26947,cl_26948,cl_26949,cl_26950,cl_26951,cl_26952,cl_26953,cl_26954,cl_26955,cl_26956,cl_26957,cl_26958,cl_26959,cl_26960,cl_26961,cl_26962,cl_26963,cl_26964,cl_26965,cl_26966,cl_26967,cl_26968,cl_26969,cl_26970,cl_26971,cl_26972,cl_26973,cl_26974,cl_26975,cl_26976,cl_26977,cl_26978,cl_26979,cl_26980,cl_26981,cl_26982,cl_26983,cl_26984,cl_26985,cl_26986,cl_26987,cl_26988,cl_26989,cl_26990,cl_26991,cl_26992,cl_26993,cl_26995,cl_26996,cl_26997,cl_26999,cl_27000,cl_27001,cl_27003,cl_27004,cl_27005,cl_27006,cl_27007,cl_27008,cl_27009,cl_27010,cl_27011,cl_27012,cl_27013,cl_27014,cl_27015,cl_27016,cl_27017,cl_27018,cl_27019,cl_27020,cl_27021,cl_27022,cl_27023,cl_27024,cl_27025,cl_27026,cl_27027,cl_27028,cl_27029,cl_27030,cl_27031,cl_27032,cl_27033,cl_27034,cl_27035,cl_27036,cl_27037,cl_27038,cl_27039,cl_27040,cl_27041,cl_27042,cl_27043,cl_27044,cl_27045,cl_27046,cl_27047,cl_27048,cl_27050,cl_27051,cl_27052,cl_27053,cl_27054,cl_27055,cl_27056,cl_27057,cl_27058,cl_27059,cl_27060,cl_27062,cl_27063,cl_27064,cl_27066,cl_27067,cl_27068,cl_27069,cl_27070,cl_27071,cl_27072,cl_27073,cl_27074,cl_27075,cl_27076,cl_27077,cl_27078,cl_27079,cl_27080,cl_27081,cl_27082,cl_27083,cl_27084,cl_27085,cl_27086,cl_27087,cl_27088,cl_27089,cl_27090,cl_27091,cl_27092,cl_27093,cl_27094,cl_27095,cl_27096,cl_27097,cl_27098,cl_27099,cl_27100,cl_27101,cl_27102,cl_27103,cl_27104,cl_27105,cl_27106,cl_27107,cl_27108,cl_27109,cl_27110,cl_27111,cl_27112,cl_27113,cl_27114,cl_27115,cl_27116,cl_27117,cl_27118,cl_27119,cl_27120,cl_27121,cl_27122,cl_27123,cl_27124,cl_27125,cl_27126,cl_27127,cl_27128,cl_27129,cl_27130,cl_27131,cl_27132,cl_27133,cl_27134,cl_27135,cl_27136,cl_27137,cl_27138,cl_27139,cl_27140,cl_27141,cl_27142,cl_27143,cl_27144,cl_27145,cl_27146,cl_27147,cl_27148,cl_27149,cl_27150,cl_27152,cl_27153,cl_27155,cl_27158,cl_27159,cl_27161,cl_27162,cl_27163,cl_27164,cl_27165,cl_27166,cl_27167,cl_27168,cl_27169,cl_27170,cl_27171,cl_27172,cl_27173,cl_27174,cl_27175,cl_27176,cl_27177,cl_27178,cl_27179,cl_27180,cl_27181,cl_27182,cl_27183,cl_27185,cl_27186,cl_27187,cl_27188,cl_27189,cl_27190,cl_27191,cl_27192,cl_27193,cl_27194,cl_27195,cl_27196,cl_27197,cl_27198,cl_27199,cl_27200,cl_27201,cl_27202,cl_27203,cl_27204,cl_27205,cl_27206,cl_27207,cl_27208,cl_27209,cl_27210,cl_27211,cl_27212,cl_27213,cl_27214,cl_27215,cl_27216,cl_27217,cl_27218,cl_27219,cl_27220,cl_27221,cl_27222,cl_27223,cl_27224,cl_27225,cl_27226,cl_27227,cl_27228,cl_27229,cl_27230,cl_27231,cl_27232,cl_27233,cl_27234,cl_27235,cl_27236,cl_27237,cl_27238,cl_27239,cl_27240,cl_27241,cl_27242,cl_27243,cl_27244,cl_27245,cl_27246,cl_27247,cl_27249,cl_27250,cl_27251,cl_27252,cl_27253,cl_27254,cl_27255,cl_27256,cl_27257,cl_27258,cl_27259,cl_27260,cl_27261,cl_27262,cl_27263,cl_27264,cl_27265,cl_27266,cl_27267,cl_27268,cl_27269,cl_27270,cl_27271,cl_27272,cl_27273,cl_27274,cl_27275,cl_27276,cl_27277,cl_27278,cl_27279,cl_27280,cl_27281,cl_27282,cl_27283,cl_27284,cl_27285,cl_27286,cl_27287,cl_27288,cl_27289,cl_27290,cl_27291,cl_27292,cl_27293,cl_27294,cl_27295,cl_27296,cl_27297,cl_27298,cl_27299,cl_27300,cl_27301,cl_27302,cl_27303]
theorem chunk_sound009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk009, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_26787 v h) (hints_cons _ _ _ (der_26788 v h) (hints_cons _ _ _ (der_26789 v h) (hints_cons _ _ _ (der_26790 v h) (hints_cons _ _ _ (der_26791 v h) (hints_cons _ _ _ (der_26792 v h) (hints_cons _ _ _ (der_26793 v h) (hints_cons _ _ _ (der_26794 v h) (hints_cons _ _ _ (der_26795 v h) (hints_cons _ _ _ (der_26796 v h) (hints_cons _ _ _ (der_26797 v h) (hints_cons _ _ _ (der_26798 v h) (hints_cons _ _ _ (der_26799 v h) (hints_cons _ _ _ (der_26800 v h) (hints_cons _ _ _ (der_26801 v h) (hints_cons _ _ _ (der_26802 v h) (hints_cons _ _ _ (der_26803 v h) (hints_cons _ _ _ (der_26804 v h) (hints_cons _ _ _ (der_26805 v h) (hints_cons _ _ _ (der_26806 v h) (hints_cons _ _ _ (der_26807 v h) (hints_cons _ _ _ (der_26808 v h) (hints_cons _ _ _ (der_26809 v h) (hints_cons _ _ _ (der_26810 v h) (hints_cons _ _ _ (der_26811 v h) (hints_cons _ _ _ (der_26812 v h) (hints_cons _ _ _ (der_26813 v h) (hints_cons _ _ _ (der_26814 v h) (hints_cons _ _ _ (der_26815 v h) (hints_cons _ _ _ (der_26816 v h) (hints_cons _ _ _ (der_26817 v h) (hints_cons _ _ _ (der_26818 v h) (hints_cons _ _ _ (der_26819 v h) (hints_cons _ _ _ (der_26820 v h) (hints_cons _ _ _ (der_26821 v h) (hints_cons _ _ _ (der_26822 v h) (hints_cons _ _ _ (der_26823 v h) (hints_cons _ _ _ (der_26824 v h) (hints_cons _ _ _ (der_26825 v h) (hints_cons _ _ _ (der_26826 v h) (hints_cons _ _ _ (der_26827 v h) (hints_cons _ _ _ (der_26828 v h) (hints_cons _ _ _ (der_26829 v h) (hints_cons _ _ _ (der_26830 v h) (hints_cons _ _ _ (der_26831 v h) (hints_cons _ _ _ (der_26832 v h) (hints_cons _ _ _ (der_26833 v h) (hints_cons _ _ _ (der_26834 v h) (hints_cons _ _ _ (der_26835 v h) (hints_cons _ _ _ (der_26836 v h) (hints_cons _ _ _ (der_26837 v h) (hints_cons _ _ _ (der_26838 v h) (hints_cons _ _ _ (der_26839 v h) (hints_cons _ _ _ (der_26840 v h) (hints_cons _ _ _ (der_26841 v h) (hints_cons _ _ _ (der_26842 v h) (hints_cons _ _ _ (der_26843 v h) (hints_cons _ _ _ (der_26844 v h) (hints_cons _ _ _ (der_26845 v h) (hints_cons _ _ _ (der_26846 v h) (hints_cons _ _ _ (der_26847 v h) (hints_cons _ _ _ (der_26848 v h) (hints_cons _ _ _ (der_26849 v h) (hints_cons _ _ _ (der_26850 v h) (hints_cons _ _ _ (der_26851 v h) (hints_cons _ _ _ (der_26852 v h) (hints_cons _ _ _ (der_26853 v h) (hints_cons _ _ _ (der_26854 v h) (hints_cons _ _ _ (der_26855 v h) (hints_cons _ _ _ (der_26856 v h) (hints_cons _ _ _ (der_26857 v h) (hints_cons _ _ _ (der_26858 v h) (hints_cons _ _ _ (der_26859 v h) (hints_cons _ _ _ (der_26860 v h) (hints_cons _ _ _ (der_26861 v h) (hints_cons _ _ _ (der_26862 v h) (hints_cons _ _ _ (der_26863 v h) (hints_cons _ _ _ (der_26864 v h) (hints_cons _ _ _ (der_26865 v h) (hints_cons _ _ _ (der_26866 v h) (hints_cons _ _ _ (der_26867 v h) (hints_cons _ _ _ (der_26868 v h) (hints_cons _ _ _ (der_26869 v h) (hints_cons _ _ _ (der_26870 v h) (hints_cons _ _ _ (der_26871 v h) (hints_cons _ _ _ (der_26872 v h) (hints_cons _ _ _ (der_26873 v h) (hints_cons _ _ _ (der_26874 v h) (hints_cons _ _ _ (der_26875 v h) (hints_cons _ _ _ (der_26876 v h) (hints_cons _ _ _ (der_26877 v h) (hints_cons _ _ _ (der_26878 v h) (hints_cons _ _ _ (der_26879 v h) (hints_cons _ _ _ (der_26880 v h) (hints_cons _ _ _ (der_26881 v h) (hints_cons _ _ _ (der_26883 v h) (hints_cons _ _ _ (der_26884 v h) (hints_cons _ _ _ (der_26885 v h) (hints_cons _ _ _ (der_26886 v h) (hints_cons _ _ _ (der_26887 v h) (hints_cons _ _ _ (der_26888 v h) (hints_cons _ _ _ (der_26889 v h) (hints_cons _ _ _ (der_26890 v h) (hints_cons _ _ _ (der_26891 v h) (hints_cons _ _ _ (der_26892 v h) (hints_cons _ _ _ (der_26893 v h) (hints_cons _ _ _ (der_26894 v h) (hints_cons _ _ _ (der_26895 v h) (hints_cons _ _ _ (der_26896 v h) (hints_cons _ _ _ (der_26897 v h) (hints_cons _ _ _ (der_26898 v h) (hints_cons _ _ _ (der_26899 v h) (hints_cons _ _ _ (der_26900 v h) (hints_cons _ _ _ (der_26901 v h) (hints_cons _ _ _ (der_26902 v h) (hints_cons _ _ _ (der_26903 v h) (hints_cons _ _ _ (der_26904 v h) (hints_cons _ _ _ (der_26905 v h) (hints_cons _ _ _ (der_26906 v h) (hints_cons _ _ _ (der_26907 v h) (hints_cons _ _ _ (der_26908 v h) (hints_cons _ _ _ (der_26909 v h) (hints_cons _ _ _ (der_26910 v h) (hints_cons _ _ _ (der_26911 v h) (hints_cons _ _ _ (der_26912 v h) (hints_cons _ _ _ (der_26914 v h) (hints_cons _ _ _ (der_26915 v h) (hints_cons _ _ _ (der_26916 v h) (hints_cons _ _ _ (der_26917 v h) (hints_cons _ _ _ (der_26918 v h) (hints_cons _ _ _ (der_26919 v h) (hints_cons _ _ _ (der_26920 v h) (hints_cons _ _ _ (der_26921 v h) (hints_cons _ _ _ (der_26922 v h) (hints_cons _ _ _ (der_26923 v h) (hints_cons _ _ _ (der_26924 v h) (hints_cons _ _ _ (der_26925 v h) (hints_cons _ _ _ (der_26926 v h) (hints_cons _ _ _ (der_26927 v h) (hints_cons _ _ _ (der_26928 v h) (hints_cons _ _ _ (der_26929 v h) (hints_cons _ _ _ (der_26930 v h) (hints_cons _ _ _ (der_26931 v h) (hints_cons _ _ _ (der_26932 v h) (hints_cons _ _ _ (der_26933 v h) (hints_cons _ _ _ (der_26934 v h) (hints_cons _ _ _ (der_26935 v h) (hints_cons _ _ _ (der_26936 v h) (hints_cons _ _ _ (der_26937 v h) (hints_cons _ _ _ (der_26938 v h) (hints_cons _ _ _ (der_26939 v h) (hints_cons _ _ _ (der_26940 v h) (hints_cons _ _ _ (der_26942 v h) (hints_cons _ _ _ (der_26943 v h) (hints_cons _ _ _ (der_26944 v h) (hints_cons _ _ _ (der_26946 v h) (hints_cons _ _ _ (der_26947 v h) (hints_cons _ _ _ (der_26948 v h) (hints_cons _ _ _ (der_26949 v h) (hints_cons _ _ _ (der_26950 v h) (hints_cons _ _ _ (der_26951 v h) (hints_cons _ _ _ (der_26952 v h) (hints_cons _ _ _ (der_26953 v h) (hints_cons _ _ _ (der_26954 v h) (hints_cons _ _ _ (der_26955 v h) (hints_cons _ _ _ (der_26956 v h) (hints_cons _ _ _ (der_26957 v h) (hints_cons _ _ _ (der_26958 v h) (hints_cons _ _ _ (der_26959 v h) (hints_cons _ _ _ (der_26960 v h) (hints_cons _ _ _ (der_26961 v h) (hints_cons _ _ _ (der_26962 v h) (hints_cons _ _ _ (der_26963 v h) (hints_cons _ _ _ (der_26964 v h) (hints_cons _ _ _ (der_26965 v h) (hints_cons _ _ _ (der_26966 v h) (hints_cons _ _ _ (der_26967 v h) (hints_cons _ _ _ (der_26968 v h) (hints_cons _ _ _ (der_26969 v h) (hints_cons _ _ _ (der_26970 v h) (hints_cons _ _ _ (der_26971 v h) (hints_cons _ _ _ (der_26972 v h) (hints_cons _ _ _ (der_26973 v h) (hints_cons _ _ _ (der_26974 v h) (hints_cons _ _ _ (der_26975 v h) (hints_cons _ _ _ (der_26976 v h) (hints_cons _ _ _ (der_26977 v h) (hints_cons _ _ _ (der_26978 v h) (hints_cons _ _ _ (der_26979 v h) (hints_cons _ _ _ (der_26980 v h) (hints_cons _ _ _ (der_26981 v h) (hints_cons _ _ _ (der_26982 v h) (hints_cons _ _ _ (der_26983 v h) (hints_cons _ _ _ (der_26984 v h) (hints_cons _ _ _ (der_26985 v h) (hints_cons _ _ _ (der_26986 v h) (hints_cons _ _ _ (der_26987 v h) (hints_cons _ _ _ (der_26988 v h) (hints_cons _ _ _ (der_26989 v h) (hints_cons _ _ _ (der_26990 v h) (hints_cons _ _ _ (der_26991 v h) (hints_cons _ _ _ (der_26992 v h) (hints_cons _ _ _ (der_26993 v h) (hints_cons _ _ _ (der_26995 v h) (hints_cons _ _ _ (der_26996 v h) (hints_cons _ _ _ (der_26997 v h) (hints_cons _ _ _ (der_26999 v h) (hints_cons _ _ _ (der_27000 v h) (hints_cons _ _ _ (der_27001 v h) (hints_cons _ _ _ (der_27003 v h) (hints_cons _ _ _ (der_27004 v h) (hints_cons _ _ _ (der_27005 v h) (hints_cons _ _ _ (der_27006 v h) (hints_cons _ _ _ (der_27007 v h) (hints_cons _ _ _ (der_27008 v h) (hints_cons _ _ _ (der_27009 v h) (hints_cons _ _ _ (der_27010 v h) (hints_cons _ _ _ (der_27011 v h) (hints_cons _ _ _ (der_27012 v h) (hints_cons _ _ _ (der_27013 v h) (hints_cons _ _ _ (der_27014 v h) (hints_cons _ _ _ (der_27015 v h) (hints_cons _ _ _ (der_27016 v h) (hints_cons _ _ _ (der_27017 v h) (hints_cons _ _ _ (der_27018 v h) (hints_cons _ _ _ (der_27019 v h) (hints_cons _ _ _ (der_27020 v h) (hints_cons _ _ _ (der_27021 v h) (hints_cons _ _ _ (der_27022 v h) (hints_cons _ _ _ (der_27023 v h) (hints_cons _ _ _ (der_27024 v h) (hints_cons _ _ _ (der_27025 v h) (hints_cons _ _ _ (der_27026 v h) (hints_cons _ _ _ (der_27027 v h) (hints_cons _ _ _ (der_27028 v h) (hints_cons _ _ _ (der_27029 v h) (hints_cons _ _ _ (der_27030 v h) (hints_cons _ _ _ (der_27031 v h) (hints_cons _ _ _ (der_27032 v h) (hints_cons _ _ _ (der_27033 v h) (hints_cons _ _ _ (der_27034 v h) (hints_cons _ _ _ (der_27035 v h) (hints_cons _ _ _ (der_27036 v h) (hints_cons _ _ _ (der_27037 v h) (hints_cons _ _ _ (der_27038 v h) (hints_cons _ _ _ (der_27039 v h) (hints_cons _ _ _ (der_27040 v h) (hints_cons _ _ _ (der_27041 v h) (hints_cons _ _ _ (der_27042 v h) (hints_cons _ _ _ (der_27043 v h) (hints_cons _ _ _ (der_27044 v h) (hints_cons _ _ _ (der_27045 v h) (hints_cons _ _ _ (der_27046 v h) (hints_cons _ _ _ (der_27047 v h) (hints_cons _ _ _ (der_27048 v h) (hints_cons _ _ _ (der_27050 v h) (hints_cons _ _ _ (der_27051 v h) (hints_cons _ _ _ (der_27052 v h) (hints_cons _ _ _ (der_27053 v h) (hints_cons _ _ _ (der_27054 v h) (hints_cons _ _ _ (der_27055 v h) (hints_cons _ _ _ (der_27056 v h) (hints_cons _ _ _ (der_27057 v h) (hints_cons _ _ _ (der_27058 v h) (hints_cons _ _ _ (der_27059 v h) (hints_cons _ _ _ (der_27060 v h) (hints_cons _ _ _ (der_27062 v h) (hints_cons _ _ _ (der_27063 v h) (hints_cons _ _ _ (der_27064 v h) (hints_cons _ _ _ (der_27066 v h) (hints_cons _ _ _ (der_27067 v h) (hints_cons _ _ _ (der_27068 v h) (hints_cons _ _ _ (der_27069 v h) (hints_cons _ _ _ (der_27070 v h) (hints_cons _ _ _ (der_27071 v h) (hints_cons _ _ _ (der_27072 v h) (hints_cons _ _ _ (der_27073 v h) (hints_cons _ _ _ (der_27074 v h) (hints_cons _ _ _ (der_27075 v h) (hints_cons _ _ _ (der_27076 v h) (hints_cons _ _ _ (der_27077 v h) (hints_cons _ _ _ (der_27078 v h) (hints_cons _ _ _ (der_27079 v h) (hints_cons _ _ _ (der_27080 v h) (hints_cons _ _ _ (der_27081 v h) (hints_cons _ _ _ (der_27082 v h) (hints_cons _ _ _ (der_27083 v h) (hints_cons _ _ _ (der_27084 v h) (hints_cons _ _ _ (der_27085 v h) (hints_cons _ _ _ (der_27086 v h) (hints_cons _ _ _ (der_27087 v h) (hints_cons _ _ _ (der_27088 v h) (hints_cons _ _ _ (der_27089 v h) (hints_cons _ _ _ (der_27090 v h) (hints_cons _ _ _ (der_27091 v h) (hints_cons _ _ _ (der_27092 v h) (hints_cons _ _ _ (der_27093 v h) (hints_cons _ _ _ (der_27094 v h) (hints_cons _ _ _ (der_27095 v h) (hints_cons _ _ _ (der_27096 v h) (hints_cons _ _ _ (der_27097 v h) (hints_cons _ _ _ (der_27098 v h) (hints_cons _ _ _ (der_27099 v h) (hints_cons _ _ _ (der_27100 v h) (hints_cons _ _ _ (der_27101 v h) (hints_cons _ _ _ (der_27102 v h) (hints_cons _ _ _ (der_27103 v h) (hints_cons _ _ _ (der_27104 v h) (hints_cons _ _ _ (der_27105 v h) (hints_cons _ _ _ (der_27106 v h) (hints_cons _ _ _ (der_27107 v h) (hints_cons _ _ _ (der_27108 v h) (hints_cons _ _ _ (der_27109 v h) (hints_cons _ _ _ (der_27110 v h) (hints_cons _ _ _ (der_27111 v h) (hints_cons _ _ _ (der_27112 v h) (hints_cons _ _ _ (der_27113 v h) (hints_cons _ _ _ (der_27114 v h) (hints_cons _ _ _ (der_27115 v h) (hints_cons _ _ _ (der_27116 v h) (hints_cons _ _ _ (der_27117 v h) (hints_cons _ _ _ (der_27118 v h) (hints_cons _ _ _ (der_27119 v h) (hints_cons _ _ _ (der_27120 v h) (hints_cons _ _ _ (der_27121 v h) (hints_cons _ _ _ (der_27122 v h) (hints_cons _ _ _ (der_27123 v h) (hints_cons _ _ _ (der_27124 v h) (hints_cons _ _ _ (der_27125 v h) (hints_cons _ _ _ (der_27126 v h) (hints_cons _ _ _ (der_27127 v h) (hints_cons _ _ _ (der_27128 v h) (hints_cons _ _ _ (der_27129 v h) (hints_cons _ _ _ (der_27130 v h) (hints_cons _ _ _ (der_27131 v h) (hints_cons _ _ _ (der_27132 v h) (hints_cons _ _ _ (der_27133 v h) (hints_cons _ _ _ (der_27134 v h) (hints_cons _ _ _ (der_27135 v h) (hints_cons _ _ _ (der_27136 v h) (hints_cons _ _ _ (der_27137 v h) (hints_cons _ _ _ (der_27138 v h) (hints_cons _ _ _ (der_27139 v h) (hints_cons _ _ _ (der_27140 v h) (hints_cons _ _ _ (der_27141 v h) (hints_cons _ _ _ (der_27142 v h) (hints_cons _ _ _ (der_27143 v h) (hints_cons _ _ _ (der_27144 v h) (hints_cons _ _ _ (der_27145 v h) (hints_cons _ _ _ (der_27146 v h) (hints_cons _ _ _ (der_27147 v h) (hints_cons _ _ _ (der_27148 v h) (hints_cons _ _ _ (der_27149 v h) (hints_cons _ _ _ (der_27150 v h) (hints_cons _ _ _ (der_27152 v h) (hints_cons _ _ _ (der_27153 v h) (hints_cons _ _ _ (der_27155 v h) (hints_cons _ _ _ (der_27158 v h) (hints_cons _ _ _ (der_27159 v h) (hints_cons _ _ _ (der_27161 v h) (hints_cons _ _ _ (der_27162 v h) (hints_cons _ _ _ (der_27163 v h) (hints_cons _ _ _ (der_27164 v h) (hints_cons _ _ _ (der_27165 v h) (hints_cons _ _ _ (der_27166 v h) (hints_cons _ _ _ (der_27167 v h) (hints_cons _ _ _ (der_27168 v h) (hints_cons _ _ _ (der_27169 v h) (hints_cons _ _ _ (der_27170 v h) (hints_cons _ _ _ (der_27171 v h) (hints_cons _ _ _ (der_27172 v h) (hints_cons _ _ _ (der_27173 v h) (hints_cons _ _ _ (der_27174 v h) (hints_cons _ _ _ (der_27175 v h) (hints_cons _ _ _ (der_27176 v h) (hints_cons _ _ _ (der_27177 v h) (hints_cons _ _ _ (der_27178 v h) (hints_cons _ _ _ (der_27179 v h) (hints_cons _ _ _ (der_27180 v h) (hints_cons _ _ _ (der_27181 v h) (hints_cons _ _ _ (der_27182 v h) (hints_cons _ _ _ (der_27183 v h) (hints_cons _ _ _ (der_27185 v h) (hints_cons _ _ _ (der_27186 v h) (hints_cons _ _ _ (der_27187 v h) (hints_cons _ _ _ (der_27188 v h) (hints_cons _ _ _ (der_27189 v h) (hints_cons _ _ _ (der_27190 v h) (hints_cons _ _ _ (der_27191 v h) (hints_cons _ _ _ (der_27192 v h) (hints_cons _ _ _ (der_27193 v h) (hints_cons _ _ _ (der_27194 v h) (hints_cons _ _ _ (der_27195 v h) (hints_cons _ _ _ (der_27196 v h) (hints_cons _ _ _ (der_27197 v h) (hints_cons _ _ _ (der_27198 v h) (hints_cons _ _ _ (der_27199 v h) (hints_cons _ _ _ (der_27200 v h) (hints_cons _ _ _ (der_27201 v h) (hints_cons _ _ _ (der_27202 v h) (hints_cons _ _ _ (der_27203 v h) (hints_cons _ _ _ (der_27204 v h) (hints_cons _ _ _ (der_27205 v h) (hints_cons _ _ _ (der_27206 v h) (hints_cons _ _ _ (der_27207 v h) (hints_cons _ _ _ (der_27208 v h) (hints_cons _ _ _ (der_27209 v h) (hints_cons _ _ _ (der_27210 v h) (hints_cons _ _ _ (der_27211 v h) (hints_cons _ _ _ (der_27212 v h) (hints_cons _ _ _ (der_27213 v h) (hints_cons _ _ _ (der_27214 v h) (hints_cons _ _ _ (der_27215 v h) (hints_cons _ _ _ (der_27216 v h) (hints_cons _ _ _ (der_27217 v h) (hints_cons _ _ _ (der_27218 v h) (hints_cons _ _ _ (der_27219 v h) (hints_cons _ _ _ (der_27220 v h) (hints_cons _ _ _ (der_27221 v h) (hints_cons _ _ _ (der_27222 v h) (hints_cons _ _ _ (der_27223 v h) (hints_cons _ _ _ (der_27224 v h) (hints_cons _ _ _ (der_27225 v h) (hints_cons _ _ _ (der_27226 v h) (hints_cons _ _ _ (der_27227 v h) (hints_cons _ _ _ (der_27228 v h) (hints_cons _ _ _ (der_27229 v h) (hints_cons _ _ _ (der_27230 v h) (hints_cons _ _ _ (der_27231 v h) (hints_cons _ _ _ (der_27232 v h) (hints_cons _ _ _ (der_27233 v h) (hints_cons _ _ _ (der_27234 v h) (hints_cons _ _ _ (der_27235 v h) (hints_cons _ _ _ (der_27236 v h) (hints_cons _ _ _ (der_27237 v h) (hints_cons _ _ _ (der_27238 v h) (hints_cons _ _ _ (der_27239 v h) (hints_cons _ _ _ (der_27240 v h) (hints_cons _ _ _ (der_27241 v h) (hints_cons _ _ _ (der_27242 v h) (hints_cons _ _ _ (der_27243 v h) (hints_cons _ _ _ (der_27244 v h) (hints_cons _ _ _ (der_27245 v h) (hints_cons _ _ _ (der_27246 v h) (hints_cons _ _ _ (der_27247 v h) (hints_cons _ _ _ (der_27249 v h) (hints_cons _ _ _ (der_27250 v h) (hints_cons _ _ _ (der_27251 v h) (hints_cons _ _ _ (der_27252 v h) (hints_cons _ _ _ (der_27253 v h) (hints_cons _ _ _ (der_27254 v h) (hints_cons _ _ _ (der_27255 v h) (hints_cons _ _ _ (der_27256 v h) (hints_cons _ _ _ (der_27257 v h) (hints_cons _ _ _ (der_27258 v h) (hints_cons _ _ _ (der_27259 v h) (hints_cons _ _ _ (der_27260 v h) (hints_cons _ _ _ (der_27261 v h) (hints_cons _ _ _ (der_27262 v h) (hints_cons _ _ _ (der_27263 v h) (hints_cons _ _ _ (der_27264 v h) (hints_cons _ _ _ (der_27265 v h) (hints_cons _ _ _ (der_27266 v h) (hints_cons _ _ _ (der_27267 v h) (hints_cons _ _ _ (der_27268 v h) (hints_cons _ _ _ (der_27269 v h) (hints_cons _ _ _ (der_27270 v h) (hints_cons _ _ _ (der_27271 v h) (hints_cons _ _ _ (der_27272 v h) (hints_cons _ _ _ (der_27273 v h) (hints_cons _ _ _ (der_27274 v h) (hints_cons _ _ _ (der_27275 v h) (hints_cons _ _ _ (der_27276 v h) (hints_cons _ _ _ (der_27277 v h) (hints_cons _ _ _ (der_27278 v h) (hints_cons _ _ _ (der_27279 v h) (hints_cons _ _ _ (der_27280 v h) (hints_cons _ _ _ (der_27281 v h) (hints_cons _ _ _ (der_27282 v h) (hints_cons _ _ _ (der_27283 v h) (hints_cons _ _ _ (der_27284 v h) (hints_cons _ _ _ (der_27285 v h) (hints_cons _ _ _ (der_27286 v h) (hints_cons _ _ _ (der_27287 v h) (hints_cons _ _ _ (der_27288 v h) (hints_cons _ _ _ (der_27289 v h) (hints_cons _ _ _ (der_27290 v h) (hints_cons _ _ _ (der_27291 v h) (hints_cons _ _ _ (der_27292 v h) (hints_cons _ _ _ (der_27293 v h) (hints_cons _ _ _ (der_27294 v h) (hints_cons _ _ _ (der_27295 v h) (hints_cons _ _ _ (der_27296 v h) (hints_cons _ _ _ (der_27297 v h) (hints_cons _ _ _ (der_27298 v h) (hints_cons _ _ _ (der_27299 v h) (hints_cons _ _ _ (der_27300 v h) (hints_cons _ _ _ (der_27301 v h) (hints_cons _ _ _ (der_27302 v h) (hints_cons _ _ _ (der_27303 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix009 := prefix008 ++ chunk009
theorem prefix_sound009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix009, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound008 v h c hc
  · exact chunk_sound009 v h c hc
end Percolation.NReplay
