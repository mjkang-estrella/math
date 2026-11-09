import NReplay010
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_27816 : CNF.NClause := [(48,false),(17,false),(64,true),(76,false),(77,false),(83,false),(70,true)]
theorem der_27816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27816 :=
  CNF.rup_sound cl_27816 [cl_6215,cl_27761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6215 v h) (hints_cons _ _ _ (der_27761 v h) (by intro d hd; cases hd)))
def cl_27817 : CNF.NClause := [(48,false),(88,true),(17,true),(64,true),(76,false),(77,false),(83,false)]
theorem der_27817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27817 :=
  CNF.rup_sound cl_27817 [cl_6216,cl_27813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6216 v h) (hints_cons _ _ _ (der_27813 v h) (by intro d hd; cases hd)))
def cl_27818 : CNF.NClause := [(48,false),(88,true),(70,false),(64,false),(77,false),(83,false),(76,true)]
theorem der_27818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27818 :=
  CNF.rup_sound cl_27818 [cl_6217,cl_26346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6217 v h) (hints_cons _ _ _ (der_26346 v h) (by intro d hd; cases hd)))
def cl_27819 : CNF.NClause := [(48,false),(17,false),(64,true),(76,true),(77,false),(70,false),(83,false)]
theorem der_27819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27819 :=
  CNF.rup_sound cl_27819 [cl_6219,cl_27764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6219 v h) (hints_cons _ _ _ (der_27764 v h) (by intro d hd; cases hd)))
def cl_27820 : CNF.NClause := [(48,false),(88,true),(17,true),(70,false),(64,true),(77,false),(83,false)]
theorem der_27820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27820 :=
  CNF.rup_sound cl_27820 [cl_6220,cl_27813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6220 v h) (hints_cons _ _ _ (der_27813 v h) (by intro d hd; cases hd)))
def cl_27821 : CNF.NClause := [(48,false),(17,false),(64,false),(76,true),(77,false),(83,false),(70,true)]
theorem der_27821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27821 :=
  CNF.rup_sound cl_27821 [cl_6221,cl_27766] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6221 v h) (hints_cons _ _ _ (der_27766 v h) (by intro d hd; cases hd)))
def cl_27822 : CNF.NClause := [(48,false),(88,true),(17,true),(64,false),(76,true),(77,false),(83,false)]
theorem der_27822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27822 :=
  CNF.rup_sound cl_27822 [cl_6222,cl_26346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6222 v h) (hints_cons _ _ _ (der_26346 v h) (by intro d hd; cases hd)))
def cl_27824 : CNF.NClause := [(48,false),(88,true),(17,true),(64,true),(77,false),(83,false),(70,true)]
theorem der_27824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27824 :=
  CNF.rup_sound cl_27824 [cl_6224,cl_27817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6224 v h) (hints_cons _ _ _ (der_27817 v h) (by intro d hd; cases hd)))
def cl_27825 : CNF.NClause := [(48,false),(17,false),(70,false),(77,true),(76,false),(83,false),(64,false)]
theorem der_27825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27825 :=
  CNF.rup_sound cl_27825 [cl_6225,cl_27770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6225 v h) (hints_cons _ _ _ (der_27770 v h) (by intro d hd; cases hd)))
def cl_27826 : CNF.NClause := [(48,false),(88,true),(17,true),(64,false),(76,false),(83,false),(70,false)]
theorem der_27826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27826 :=
  CNF.rup_sound cl_27826 [cl_6226,cl_27813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6226 v h) (hints_cons _ _ _ (der_27813 v h) (by intro d hd; cases hd)))
def cl_27827 : CNF.NClause := [(48,false),(17,false),(64,true),(76,false),(77,true),(70,false),(83,false)]
theorem der_27827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27827 :=
  CNF.rup_sound cl_27827 [cl_6227,cl_27770] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6227 v h) (hints_cons _ _ _ (der_27770 v h) (by intro d hd; cases hd)))
def cl_27828 : CNF.NClause := [(48,false),(88,true),(17,true),(70,false),(64,true),(83,false),(76,false)]
theorem der_27828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27828 :=
  CNF.rup_sound cl_27828 [cl_6228,cl_27813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6228 v h) (hints_cons _ _ _ (der_27813 v h) (by intro d hd; cases hd)))
def cl_27829 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(76,false),(70,true),(83,false)]
theorem der_27829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27829 :=
  CNF.rup_sound cl_27829 [cl_6229,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6229 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27830 : CNF.NClause := [(48,false),(77,true),(17,true),(64,false),(76,false),(70,true),(83,false)]
theorem der_27830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27830 :=
  CNF.rup_sound cl_27830 [cl_6230,cl_27773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6230 v h) (hints_cons _ _ _ (der_27773 v h) (by intro d hd; cases hd)))
def cl_27831 : CNF.NClause := [(48,false),(77,true),(17,false),(76,false),(70,true),(83,false),(88,true)]
theorem der_27831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27831 :=
  CNF.rup_sound cl_27831 [cl_6231,cl_27829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6231 v h) (hints_cons _ _ _ (der_27829 v h) (by intro d hd; cases hd)))
def cl_27832 : CNF.NClause := [(48,false),(17,true),(64,true),(76,false),(70,true),(83,false),(88,true)]
theorem der_27832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27832 :=
  CNF.rup_sound cl_27832 [cl_6232,cl_27817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6232 v h) (hints_cons _ _ _ (der_27817 v h) (by intro d hd; cases hd)))
def cl_27833 : CNF.NClause := [(48,false),(88,true),(70,false),(64,false),(76,true),(77,true),(83,false)]
theorem der_27833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27833 :=
  CNF.rup_sound cl_27833 [cl_6233,cl_26348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6233 v h) (hints_cons _ _ _ (der_26348 v h) (by intro d hd; cases hd)))
def cl_27834 : CNF.NClause := [(48,false),(88,true),(17,false),(64,true),(76,true),(70,false),(83,false)]
theorem der_27834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27834 :=
  CNF.rup_sound cl_27834 [cl_6235,cl_27819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6235 v h) (hints_cons _ _ _ (der_27819 v h) (by intro d hd; cases hd)))
def cl_27835 : CNF.NClause := [(48,false),(88,true),(17,true),(70,false),(76,true),(77,true),(83,false)]
theorem der_27835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27835 :=
  CNF.rup_sound cl_27835 [cl_6236,cl_26348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6236 v h) (hints_cons _ _ _ (der_26348 v h) (by intro d hd; cases hd)))
def cl_27836 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(76,true),(70,true),(83,false)]
theorem der_27836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27836 :=
  CNF.rup_sound cl_27836 [cl_6237,cl_27779] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6237 v h) (hints_cons _ _ _ (der_27779 v h) (by intro d hd; cases hd)))
def cl_27837 : CNF.NClause := [(48,false),(17,true),(64,false),(76,true),(70,true),(83,false),(88,true)]
theorem der_27837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27837 :=
  CNF.rup_sound cl_27837 [cl_6238,cl_27822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6238 v h) (hints_cons _ _ _ (der_27822 v h) (by intro d hd; cases hd)))
def cl_27838 : CNF.NClause := [(48,false),(77,true),(17,false),(76,true),(70,true),(83,false),(88,true)]
theorem der_27838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27838 :=
  CNF.rup_sound cl_27838 [cl_6239,cl_27836] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6239 v h) (hints_cons _ _ _ (der_27836 v h) (by intro d hd; cases hd)))
def cl_27839 : CNF.NClause := [(48,false),(77,true),(17,true),(64,true),(76,true),(83,false),(88,true)]
theorem der_27839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27839 :=
  CNF.rup_sound cl_27839 [cl_6240,cl_27835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6240 v h) (hints_cons _ _ _ (der_27835 v h) (by intro d hd; cases hd)))
def cl_27840 : CNF.NClause := [(48,false),(83,true),(17,false),(70,false),(64,false),(77,false),(76,false)]
theorem der_27840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27840 :=
  CNF.rup_sound cl_27840 [cl_6241,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6241 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27841 : CNF.NClause := [(48,false),(83,true),(17,false),(64,true),(76,false),(77,false),(70,false)]
theorem der_27841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27841 :=
  CNF.rup_sound cl_27841 [cl_6243,cl_27784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6243 v h) (hints_cons _ _ _ (der_27784 v h) (by intro d hd; cases hd)))
def cl_27842 : CNF.NClause := [(48,false),(17,true),(70,false),(64,true),(77,false),(76,false),(88,true)]
theorem der_27842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27842 :=
  CNF.rup_sound cl_27842 [cl_6244,cl_27813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6244 v h) (hints_cons _ _ _ (der_27813 v h) (by intro d hd; cases hd)))
def cl_27843 : CNF.NClause := [(48,false),(83,true),(17,false),(64,false),(76,false),(77,false),(70,true)]
theorem der_27843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27843 :=
  CNF.rup_sound cl_27843 [cl_6245,cl_27786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6245 v h) (hints_cons _ _ _ (der_27786 v h) (by intro d hd; cases hd)))
def cl_27844 : CNF.NClause := [(48,false),(83,true),(17,true),(64,false),(76,false),(77,false),(70,true)]
theorem der_27844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27844 :=
  CNF.rup_sound cl_27844 [cl_6246,cl_27789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6246 v h) (hints_cons _ _ _ (der_27789 v h) (by intro d hd; cases hd)))
def cl_27845 : CNF.NClause := [(48,false),(83,true),(17,false),(64,true),(76,false),(77,false),(70,true)]
theorem der_27845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27845 :=
  CNF.rup_sound cl_27845 [cl_6247,cl_27788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6247 v h) (hints_cons _ _ _ (der_27788 v h) (by intro d hd; cases hd)))
def cl_27846 : CNF.NClause := [(48,false),(17,true),(64,true),(76,false),(77,false),(70,true),(88,true)]
theorem der_27846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27846 :=
  CNF.rup_sound cl_27846 [cl_6248,cl_27817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6248 v h) (hints_cons _ _ _ (der_27817 v h) (by intro d hd; cases hd)))
def cl_27847 : CNF.NClause := [(48,false),(83,true),(17,false),(70,false),(64,false),(77,false),(76,true)]
theorem der_27847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27847 :=
  CNF.rup_sound cl_27847 [cl_6249,cl_27790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6249 v h) (hints_cons _ _ _ (der_27790 v h) (by intro d hd; cases hd)))
def cl_27849 : CNF.NClause := [(48,false),(83,true),(17,true),(70,false),(64,true),(77,false),(76,true)]
theorem der_27849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27849 :=
  CNF.rup_sound cl_27849 [cl_6252,cl_27792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6252 v h) (hints_cons _ _ _ (der_27792 v h) (by intro d hd; cases hd)))
def cl_27850 : CNF.NClause := [(48,false),(83,true),(17,false),(64,false),(76,true),(77,false),(70,true)]
theorem der_27850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27850 :=
  CNF.rup_sound cl_27850 [cl_6253,cl_27795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6253 v h) (hints_cons _ _ _ (der_27795 v h) (by intro d hd; cases hd)))
def cl_27851 : CNF.NClause := [(48,false),(17,true),(64,false),(76,true),(77,false),(70,true),(88,true)]
theorem der_27851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27851 :=
  CNF.rup_sound cl_27851 [cl_6254,cl_27822] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6254 v h) (hints_cons _ _ _ (der_27822 v h) (by intro d hd; cases hd)))
def cl_27853 : CNF.NClause := [(48,false),(17,true),(64,true),(76,true),(77,false),(70,true),(88,true)]
theorem der_27853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27853 :=
  CNF.rup_sound cl_27853 [cl_6256,cl_27824] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6256 v h) (hints_cons _ _ _ (der_27824 v h) (by intro d hd; cases hd)))
def cl_27855 : CNF.NClause := [(48,false),(83,true),(17,false),(64,true),(76,false),(77,true),(70,false)]
theorem der_27855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27855 :=
  CNF.rup_sound cl_27855 [cl_6259,cl_27798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6259 v h) (hints_cons _ _ _ (der_27798 v h) (by intro d hd; cases hd)))
def cl_27856 : CNF.NClause := [(48,false),(83,true),(70,false),(64,true),(77,true),(76,false),(88,true)]
theorem der_27856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27856 :=
  CNF.rup_sound cl_27856 [cl_6260,cl_27855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6260 v h) (hints_cons _ _ _ (der_27855 v h) (by intro d hd; cases hd)))
def cl_27857 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(76,false),(70,true),(88,true)]
theorem der_27857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27857 :=
  CNF.rup_sound cl_27857 [cl_6261,cl_27829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6261 v h) (hints_cons _ _ _ (der_27829 v h) (by intro d hd; cases hd)))
def cl_27858 : CNF.NClause := [(48,false),(17,true),(64,false),(76,false),(70,true),(83,true),(88,true)]
theorem der_27858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27858 :=
  CNF.rup_sound cl_27858 [cl_6262,cl_27844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6262 v h) (hints_cons _ _ _ (der_27844 v h) (by intro d hd; cases hd)))
def cl_27859 : CNF.NClause := [(48,false),(77,true),(17,false),(64,true),(76,false),(83,true),(88,true)]
theorem der_27859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27859 :=
  CNF.rup_sound cl_27859 [cl_6263,cl_27855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6263 v h) (hints_cons _ _ _ (der_27855 v h) (by intro d hd; cases hd)))
def cl_27860 : CNF.NClause := [(48,false),(77,true),(64,true),(76,false),(70,true),(83,true),(88,true)]
theorem der_27860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27860 :=
  CNF.rup_sound cl_27860 [cl_6264,cl_27859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6264 v h) (hints_cons _ _ _ (der_27859 v h) (by intro d hd; cases hd)))
def cl_27863 : CNF.NClause := [(48,false),(17,true),(70,false),(64,true),(76,true),(77,true),(88,true)]
theorem der_27863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27863 :=
  CNF.rup_sound cl_27863 [cl_6268,cl_27835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6268 v h) (hints_cons _ _ _ (der_27835 v h) (by intro d hd; cases hd)))
def cl_27864 : CNF.NClause := [(48,false),(77,true),(17,false),(64,false),(76,true),(70,true),(83,true)]
theorem der_27864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27864 :=
  CNF.rup_sound cl_27864 [cl_6269,cl_27807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6269 v h) (hints_cons _ _ _ (der_27807 v h) (by intro d hd; cases hd)))
def cl_27865 : CNF.NClause := [(48,false),(17,true),(64,false),(76,true),(70,true),(83,true),(88,true)]
theorem der_27865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27865 :=
  CNF.rup_sound cl_27865 [cl_6270,cl_27851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6270 v h) (hints_cons _ _ _ (der_27851 v h) (by intro d hd; cases hd)))
def cl_27867 : CNF.NClause := [(48,false),(77,true),(17,true),(64,true),(76,true),(83,true),(88,true)]
theorem der_27867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27867 :=
  CNF.rup_sound cl_27867 [cl_6272,cl_27863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6272 v h) (hints_cons _ _ _ (der_27863 v h) (by intro d hd; cases hd)))
def cl_27868 : CNF.NClause := [(43,false),(68,false),(81,false),(64,true),(91,false),(85,false),(72,false)]
theorem der_27868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27868 :=
  CNF.rup_sound cl_27868 [cl_5508,cl_5507] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5508 v h) (hints_cons _ _ _ (inp_5507 v h) (by intro d hd; cases hd)))
def cl_27869 : CNF.NClause := [(43,false),(68,true),(72,false),(91,false),(81,false),(85,false),(64,false)]
theorem der_27869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27869 :=
  CNF.rup_sound cl_27869 [cl_5510,cl_5509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5510 v h) (hints_cons _ _ _ (inp_5509 v h) (by intro d hd; cases hd)))
def cl_27870 : CNF.NClause := [(43,false),(64,true),(12,false),(72,false),(81,false),(85,false),(91,false)]
theorem der_27870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27870 :=
  CNF.rup_sound cl_27870 [cl_5511,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5511 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27871 : CNF.NClause := [(43,false),(12,true),(81,false),(64,true),(85,false),(72,false),(91,false)]
theorem der_27871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27871 :=
  CNF.rup_sound cl_27871 [cl_5512,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5512 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27872 : CNF.NClause := [(43,false),(68,false),(72,true),(64,false),(85,false),(91,false),(81,false)]
theorem der_27872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27872 :=
  CNF.rup_sound cl_27872 [cl_5514,cl_5513] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5514 v h) (hints_cons _ _ _ (inp_5513 v h) (by intro d hd; cases hd)))
def cl_27873 : CNF.NClause := [(43,false),(12,false),(91,false),(68,false),(64,true),(81,false),(85,false)]
theorem der_27873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27873 :=
  CNF.rup_sound cl_27873 [cl_5515,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5515 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27874 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(91,false),(81,false),(85,false)]
theorem der_27874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27874 :=
  CNF.rup_sound cl_27874 [cl_5516,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5516 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27875 : CNF.NClause := [(43,false),(68,true),(12,false),(64,false),(81,false),(85,false),(91,false)]
theorem der_27875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27875 :=
  CNF.rup_sound cl_27875 [cl_5517,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5517 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27876 : CNF.NClause := [(43,false),(68,true),(12,true),(64,false),(81,false),(85,false),(91,false)]
theorem der_27876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27876 :=
  CNF.rup_sound cl_27876 [cl_5518,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5518 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27877 : CNF.NClause := [(43,false),(68,true),(12,false),(64,true),(81,false),(85,false),(91,false)]
theorem der_27877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27877 :=
  CNF.rup_sound cl_27877 [cl_5519,cl_27870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5519 v h) (hints_cons _ _ _ (der_27870 v h) (by intro d hd; cases hd)))
def cl_27878 : CNF.NClause := [(43,false),(68,true),(72,true),(64,true),(81,false),(85,false),(91,false)]
theorem der_27878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27878 :=
  CNF.rup_sound cl_27878 [cl_5520,cl_27877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5520 v h) (hints_cons _ _ _ (der_27877 v h) (by intro d hd; cases hd)))
def cl_27879 : CNF.NClause := [(43,false),(81,true),(68,false),(72,false),(64,false),(85,false),(91,false)]
theorem der_27879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27879 :=
  CNF.rup_sound cl_27879 [cl_5522,cl_5521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5522 v h) (hints_cons _ _ _ (inp_5521 v h) (by intro d hd; cases hd)))
def cl_27880 : CNF.NClause := [(43,false),(12,false),(64,true),(72,false),(68,false),(85,false),(91,false)]
theorem der_27880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27880 :=
  CNF.rup_sound cl_27880 [cl_5523,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5523 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27881 : CNF.NClause := [(43,false),(12,true),(64,true),(68,false),(72,false),(85,false),(91,false)]
theorem der_27881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27881 :=
  CNF.rup_sound cl_27881 [cl_5524,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5524 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27882 : CNF.NClause := [(43,false),(12,false),(68,true),(64,false),(72,false),(85,false),(91,false)]
theorem der_27882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27882 :=
  CNF.rup_sound cl_27882 [cl_5525,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5525 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27883 : CNF.NClause := [(43,false),(12,true),(68,true),(64,false),(72,false),(85,false),(91,false)]
theorem der_27883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27883 :=
  CNF.rup_sound cl_27883 [cl_5526,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5526 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27884 : CNF.NClause := [(43,false),(12,false),(68,true),(72,false),(64,true),(85,false),(91,false)]
theorem der_27884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27884 :=
  CNF.rup_sound cl_27884 [cl_5527,cl_27870] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5527 v h) (hints_cons _ _ _ (der_27870 v h) (by intro d hd; cases hd)))
def cl_27885 : CNF.NClause := [(43,false),(81,true),(68,true),(64,true),(72,false),(85,false),(91,false)]
theorem der_27885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27885 :=
  CNF.rup_sound cl_27885 [cl_5528,cl_27884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5528 v h) (hints_cons _ _ _ (der_27884 v h) (by intro d hd; cases hd)))
def cl_27886 : CNF.NClause := [(43,false),(12,false),(64,false),(72,true),(68,false),(85,false),(91,false)]
theorem der_27886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27886 :=
  CNF.rup_sound cl_27886 [cl_5529,cl_27872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5529 v h) (hints_cons _ _ _ (der_27872 v h) (by intro d hd; cases hd)))
def cl_27887 : CNF.NClause := [(43,false),(12,true),(68,false),(72,true),(64,false),(85,false),(91,false)]
theorem der_27887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27887 :=
  CNF.rup_sound cl_27887 [cl_5530,cl_27872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5530 v h) (hints_cons _ _ _ (der_27872 v h) (by intro d hd; cases hd)))
def cl_27888 : CNF.NClause := [(43,false),(12,false),(64,true),(68,false),(72,true),(85,false),(91,false)]
theorem der_27888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27888 :=
  CNF.rup_sound cl_27888 [cl_5531,cl_27873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5531 v h) (hints_cons _ _ _ (der_27873 v h) (by intro d hd; cases hd)))
def cl_27889 : CNF.NClause := [(43,false),(81,true),(64,true),(72,true),(68,false),(85,false),(91,false)]
theorem der_27889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27889 :=
  CNF.rup_sound cl_27889 [cl_5532,cl_27888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5532 v h) (hints_cons _ _ _ (der_27888 v h) (by intro d hd; cases hd)))
def cl_27890 : CNF.NClause := [(43,false),(12,false),(68,true),(64,false),(72,true),(85,false),(91,false)]
theorem der_27890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27890 :=
  CNF.rup_sound cl_27890 [cl_5533,cl_27875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5533 v h) (hints_cons _ _ _ (der_27875 v h) (by intro d hd; cases hd)))
def cl_27891 : CNF.NClause := [(43,false),(81,true),(68,true),(64,false),(72,true),(85,false),(91,false)]
theorem der_27891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27891 :=
  CNF.rup_sound cl_27891 [cl_5534,cl_27890] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5534 v h) (hints_cons _ _ _ (der_27890 v h) (by intro d hd; cases hd)))
def cl_27892 : CNF.NClause := [(43,false),(12,false),(68,true),(64,true),(72,true),(85,false),(91,false)]
theorem der_27892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27892 :=
  CNF.rup_sound cl_27892 [cl_5535,cl_27878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5535 v h) (hints_cons _ _ _ (der_27878 v h) (by intro d hd; cases hd)))
def cl_27893 : CNF.NClause := [(43,false),(12,true),(68,true),(64,true),(72,true),(85,false),(91,false)]
theorem der_27893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27893 :=
  CNF.rup_sound cl_27893 [cl_5536,cl_27878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5536 v h) (hints_cons _ _ _ (der_27878 v h) (by intro d hd; cases hd)))
def cl_27894 : CNF.NClause := [(43,false),(12,true),(64,false),(72,false),(68,false),(81,false),(91,false)]
theorem der_27894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27894 :=
  CNF.rup_sound cl_27894 [cl_5538,cl_5506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5538 v h) (hints_cons _ _ _ (inp_5506 v h) (by intro d hd; cases hd)))
def cl_27895 : CNF.NClause := [(43,false),(12,false),(64,true),(72,false),(81,false),(68,false),(91,false)]
theorem der_27895 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27895 :=
  CNF.rup_sound cl_27895 [cl_5539,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5539 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27896 : CNF.NClause := [(43,false),(12,true),(64,true),(91,false),(68,false),(72,false),(81,false)]
theorem der_27896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27896 :=
  CNF.rup_sound cl_27896 [cl_5540,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5540 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27897 : CNF.NClause := [(43,false),(12,false),(68,true),(64,false),(72,false),(81,false),(91,false)]
theorem der_27897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27897 :=
  CNF.rup_sound cl_27897 [cl_5541,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5541 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27898 : CNF.NClause := [(43,false),(68,true),(12,true),(72,false),(64,false),(81,false),(91,false)]
theorem der_27898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27898 :=
  CNF.rup_sound cl_27898 [cl_5542,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5542 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27899 : CNF.NClause := [(43,false),(12,false),(68,true),(72,false),(81,false),(64,true),(91,false)]
theorem der_27899 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27899 :=
  CNF.rup_sound cl_27899 [cl_5543,cl_27884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5543 v h) (hints_cons _ _ _ (der_27884 v h) (by intro d hd; cases hd)))
def cl_27900 : CNF.NClause := [(43,false),(68,true),(85,true),(72,false),(81,false),(64,true),(91,false)]
theorem der_27900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27900 :=
  CNF.rup_sound cl_27900 [cl_5544,cl_27899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5544 v h) (hints_cons _ _ _ (der_27899 v h) (by intro d hd; cases hd)))
def cl_27901 : CNF.NClause := [(43,false),(72,true),(12,false),(81,false),(68,false),(64,false),(91,false)]
theorem der_27901 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27901 :=
  CNF.rup_sound cl_27901 [cl_5545,cl_27872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5545 v h) (hints_cons _ _ _ (der_27872 v h) (by intro d hd; cases hd)))
def cl_27902 : CNF.NClause := [(43,false),(72,true),(12,true),(81,false),(68,false),(64,false),(91,false)]
theorem der_27902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27902 :=
  CNF.rup_sound cl_27902 [cl_5546,cl_27872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5546 v h) (hints_cons _ _ _ (der_27872 v h) (by intro d hd; cases hd)))
def cl_27903 : CNF.NClause := [(43,false),(72,true),(12,false),(81,false),(68,false),(64,true),(91,false)]
theorem der_27903 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27903 :=
  CNF.rup_sound cl_27903 [cl_5547,cl_27873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5547 v h) (hints_cons _ _ _ (der_27873 v h) (by intro d hd; cases hd)))
def cl_27904 : CNF.NClause := [(43,false),(72,true),(12,true),(68,false),(64,true),(81,false),(91,false)]
theorem der_27904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27904 :=
  CNF.rup_sound cl_27904 [cl_5548,cl_27874] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5548 v h) (hints_cons _ _ _ (der_27874 v h) (by intro d hd; cases hd)))
def cl_27905 : CNF.NClause := [(43,false),(72,true),(12,false),(68,true),(64,false),(81,false),(91,false)]
theorem der_27905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27905 :=
  CNF.rup_sound cl_27905 [cl_5549,cl_27875] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5549 v h) (hints_cons _ _ _ (der_27875 v h) (by intro d hd; cases hd)))
def cl_27906 : CNF.NClause := [(43,false),(72,true),(12,true),(68,true),(64,false),(81,false),(91,false)]
theorem der_27906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27906 :=
  CNF.rup_sound cl_27906 [cl_5550,cl_27876] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5550 v h) (hints_cons _ _ _ (der_27876 v h) (by intro d hd; cases hd)))
def cl_27907 : CNF.NClause := [(43,false),(72,true),(12,false),(68,true),(64,true),(81,false),(91,false)]
theorem der_27907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27907 :=
  CNF.rup_sound cl_27907 [cl_5551,cl_27878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5551 v h) (hints_cons _ _ _ (der_27878 v h) (by intro d hd; cases hd)))
def cl_27908 : CNF.NClause := [(43,false),(72,true),(12,true),(68,true),(64,true),(81,false),(91,false)]
theorem der_27908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27908 :=
  CNF.rup_sound cl_27908 [cl_5552,cl_27878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5552 v h) (hints_cons _ _ _ (der_27878 v h) (by intro d hd; cases hd)))
def cl_27909 : CNF.NClause := [(43,false),(81,true),(12,false),(64,false),(72,false),(68,false),(91,false)]
theorem der_27909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27909 :=
  CNF.rup_sound cl_27909 [cl_5553,cl_27879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5553 v h) (hints_cons _ _ _ (der_27879 v h) (by intro d hd; cases hd)))
def cl_27910 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(72,false),(64,false),(91,false)]
theorem der_27910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27910 :=
  CNF.rup_sound cl_27910 [cl_5554,cl_27879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5554 v h) (hints_cons _ _ _ (der_27879 v h) (by intro d hd; cases hd)))
def cl_27911 : CNF.NClause := [(43,false),(12,false),(64,true),(72,false),(68,false),(85,true),(91,false)]
theorem der_27911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27911 :=
  CNF.rup_sound cl_27911 [cl_5555,cl_27895] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5555 v h) (hints_cons _ _ _ (der_27895 v h) (by intro d hd; cases hd)))
def cl_27912 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(72,false),(85,true),(91,false)]
theorem der_27912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27912 :=
  CNF.rup_sound cl_27912 [cl_5556,cl_27910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5556 v h) (hints_cons _ _ _ (der_27910 v h) (by intro d hd; cases hd)))
def cl_27913 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(64,false),(72,false),(91,false)]
theorem der_27913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27913 :=
  CNF.rup_sound cl_27913 [cl_5557,cl_27882] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5557 v h) (hints_cons _ _ _ (der_27882 v h) (by intro d hd; cases hd)))
def cl_27914 : CNF.NClause := [(43,false),(81,true),(12,true),(64,false),(72,false),(85,true),(91,false)]
theorem der_27914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27914 :=
  CNF.rup_sound cl_27914 [cl_5558,cl_27910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5558 v h) (hints_cons _ _ _ (der_27910 v h) (by intro d hd; cases hd)))
def cl_27915 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(72,false),(64,true),(91,false)]
theorem der_27915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27915 :=
  CNF.rup_sound cl_27915 [cl_5559,cl_27884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5559 v h) (hints_cons _ _ _ (der_27884 v h) (by intro d hd; cases hd)))
def cl_27916 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(72,false),(64,true),(91,false)]
theorem der_27916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27916 :=
  CNF.rup_sound cl_27916 [cl_5560,cl_27885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5560 v h) (hints_cons _ _ _ (der_27885 v h) (by intro d hd; cases hd)))
def cl_27917 : CNF.NClause := [(43,false),(81,true),(12,false),(64,false),(72,true),(68,false),(91,false)]
theorem der_27917 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27917 :=
  CNF.rup_sound cl_27917 [cl_5561,cl_27886] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5561 v h) (hints_cons _ _ _ (der_27886 v h) (by intro d hd; cases hd)))
def cl_27918 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(64,false),(85,true),(91,false)]
theorem der_27918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27918 :=
  CNF.rup_sound cl_27918 [cl_5562,cl_27910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5562 v h) (hints_cons _ _ _ (der_27910 v h) (by intro d hd; cases hd)))
def cl_27919 : CNF.NClause := [(43,false),(81,true),(12,false),(64,true),(68,false),(72,true),(91,false)]
theorem der_27919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27919 :=
  CNF.rup_sound cl_27919 [cl_5563,cl_27889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5563 v h) (hints_cons _ _ _ (der_27889 v h) (by intro d hd; cases hd)))
def cl_27920 : CNF.NClause := [(43,false),(81,true),(12,true),(64,true),(72,true),(68,false),(91,false)]
theorem der_27920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27920 :=
  CNF.rup_sound cl_27920 [cl_5564,cl_27889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5564 v h) (hints_cons _ _ _ (der_27889 v h) (by intro d hd; cases hd)))
def cl_27921 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(64,false),(72,true),(91,false)]
theorem der_27921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27921 :=
  CNF.rup_sound cl_27921 [cl_5565,cl_27891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5565 v h) (hints_cons _ _ _ (der_27891 v h) (by intro d hd; cases hd)))
def cl_27922 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(64,false),(72,true),(91,false)]
theorem der_27922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27922 :=
  CNF.rup_sound cl_27922 [cl_5566,cl_27891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5566 v h) (hints_cons _ _ _ (der_27891 v h) (by intro d hd; cases hd)))
def cl_27923 : CNF.NClause := [(43,false),(12,false),(68,true),(64,true),(72,true),(85,true),(91,false)]
theorem der_27923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27923 :=
  CNF.rup_sound cl_27923 [cl_5567,cl_27907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5567 v h) (hints_cons _ _ _ (der_27907 v h) (by intro d hd; cases hd)))
def cl_27924 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(64,true),(85,true),(91,false)]
theorem der_27924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27924 :=
  CNF.rup_sound cl_27924 [cl_5568,cl_27916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5568 v h) (hints_cons _ _ _ (der_27916 v h) (by intro d hd; cases hd)))
def cl_27925 : CNF.NClause := [(43,false),(68,false),(12,true),(85,false),(81,false),(64,false),(72,false)]
theorem der_27925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27925 :=
  CNF.rup_sound cl_27925 [cl_5570,cl_5506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5570 v h) (hints_cons _ _ _ (inp_5506 v h) (by intro d hd; cases hd)))
def cl_27926 : CNF.NClause := [(43,false),(64,true),(12,false),(68,false),(72,false),(81,false),(85,false)]
theorem der_27926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27926 :=
  CNF.rup_sound cl_27926 [cl_5571,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5571 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27927 : CNF.NClause := [(43,false),(68,false),(12,true),(64,true),(72,false),(85,false),(81,false)]
theorem der_27927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27927 :=
  CNF.rup_sound cl_27927 [cl_5572,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5572 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_27928 : CNF.NClause := [(43,false),(68,true),(12,false),(72,false),(85,false),(64,false),(81,false)]
theorem der_27928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27928 :=
  CNF.rup_sound cl_27928 [cl_5573,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5573 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27929 : CNF.NClause := [(43,false),(68,true),(12,true),(81,false),(64,false),(72,false),(85,false)]
theorem der_27929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27929 :=
  CNF.rup_sound cl_27929 [cl_5574,cl_27869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5574 v h) (hints_cons _ _ _ (der_27869 v h) (by intro d hd; cases hd)))
def cl_27930 : CNF.NClause := [(43,false),(64,true),(12,false),(68,true),(72,false),(81,false),(85,false)]
theorem der_27930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27930 :=
  CNF.rup_sound cl_27930 [cl_5575,cl_27884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5575 v h) (hints_cons _ _ _ (der_27884 v h) (by intro d hd; cases hd)))
def cl_27931 : CNF.NClause := [(43,false),(68,true),(12,true),(64,true),(72,false),(81,false),(85,false)]
theorem der_27931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27931 :=
  CNF.rup_sound cl_27931 [cl_5576,cl_27871] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5576 v h) (hints_cons _ _ _ (der_27871 v h) (by intro d hd; cases hd)))
def cl_27932 : CNF.NClause := [(43,false),(72,true),(12,false),(64,false),(68,false),(85,false),(81,false)]
theorem der_27932 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27932 :=
  CNF.rup_sound cl_27932 [cl_5577,cl_27872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5577 v h) (hints_cons _ _ _ (der_27872 v h) (by intro d hd; cases hd)))
def cl_27933 : CNF.NClause := [(43,false),(72,true),(12,true),(68,false),(85,false),(64,false),(81,false)]
theorem der_27933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27933 :=
  CNF.rup_sound cl_27933 [cl_5578,cl_27872] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5578 v h) (hints_cons _ _ _ (der_27872 v h) (by intro d hd; cases hd)))
def cl_27934 : CNF.NClause := [(43,false),(72,true),(12,false),(85,false),(68,false),(64,true),(81,false)]
theorem der_27934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27934 :=
  CNF.rup_sound cl_27934 [cl_5579,cl_27873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5579 v h) (hints_cons _ _ _ (der_27873 v h) (by intro d hd; cases hd)))
def cl_27935 : CNF.NClause := [(43,false),(72,true),(12,true),(68,false),(81,false),(85,false),(91,true)]
theorem der_27935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27935 :=
  CNF.rup_sound cl_27935 [cl_5580,cl_27933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5580 v h) (hints_cons _ _ _ (der_27933 v h) (by intro d hd; cases hd)))
def cl_27936 : CNF.NClause := [(43,false),(12,false),(72,true),(64,false),(81,false),(85,false),(91,true)]
theorem der_27936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27936 :=
  CNF.rup_sound cl_27936 [cl_5581,cl_27932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5581 v h) (hints_cons _ _ _ (der_27932 v h) (by intro d hd; cases hd)))
def cl_27937 : CNF.NClause := [(43,false),(72,true),(12,true),(64,false),(81,false),(85,false),(91,true)]
theorem der_27937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27937 :=
  CNF.rup_sound cl_27937 [cl_5582,cl_27933] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5582 v h) (hints_cons _ _ _ (der_27933 v h) (by intro d hd; cases hd)))
def cl_27938 : CNF.NClause := [(43,false),(72,true),(12,false),(68,true),(64,true),(81,false),(85,false)]
theorem der_27938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27938 :=
  CNF.rup_sound cl_27938 [cl_5583,cl_27878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5583 v h) (hints_cons _ _ _ (der_27878 v h) (by intro d hd; cases hd)))
def cl_27939 : CNF.NClause := [(43,false),(72,true),(12,true),(68,true),(64,true),(81,false),(85,false)]
theorem der_27939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27939 :=
  CNF.rup_sound cl_27939 [cl_5584,cl_27878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5584 v h) (hints_cons _ _ _ (der_27878 v h) (by intro d hd; cases hd)))
def cl_27940 : CNF.NClause := [(43,false),(81,true),(12,false),(64,false),(72,false),(68,false),(85,false)]
theorem der_27940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27940 :=
  CNF.rup_sound cl_27940 [cl_5585,cl_27879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5585 v h) (hints_cons _ _ _ (der_27879 v h) (by intro d hd; cases hd)))
def cl_27941 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(72,false),(64,false),(85,false)]
theorem der_27941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27941 :=
  CNF.rup_sound cl_27941 [cl_5586,cl_27879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5586 v h) (hints_cons _ _ _ (der_27879 v h) (by intro d hd; cases hd)))
def cl_27942 : CNF.NClause := [(43,false),(12,false),(64,true),(72,false),(68,false),(85,false),(91,true)]
theorem der_27942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27942 :=
  CNF.rup_sound cl_27942 [cl_5587,cl_27926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5587 v h) (hints_cons _ _ _ (der_27926 v h) (by intro d hd; cases hd)))
def cl_27943 : CNF.NClause := [(43,false),(81,true),(12,true),(64,true),(68,false),(72,false),(85,false)]
theorem der_27943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27943 :=
  CNF.rup_sound cl_27943 [cl_5588,cl_27881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5588 v h) (hints_cons _ _ _ (der_27881 v h) (by intro d hd; cases hd)))
def cl_27944 : CNF.NClause := [(43,false),(81,true),(12,false),(64,false),(72,false),(85,false),(91,true)]
theorem der_27944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27944 :=
  CNF.rup_sound cl_27944 [cl_5589,cl_27940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5589 v h) (hints_cons _ _ _ (der_27940 v h) (by intro d hd; cases hd)))
def cl_27945 : CNF.NClause := [(43,false),(12,true),(68,true),(64,false),(72,false),(85,false),(91,true)]
theorem der_27945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27945 :=
  CNF.rup_sound cl_27945 [cl_5590,cl_27929] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5590 v h) (hints_cons _ _ _ (der_27929 v h) (by intro d hd; cases hd)))
def cl_27946 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(72,false),(64,true),(85,false)]
theorem der_27946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27946 :=
  CNF.rup_sound cl_27946 [cl_5591,cl_27884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5591 v h) (hints_cons _ _ _ (der_27884 v h) (by intro d hd; cases hd)))
def cl_27947 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(72,false),(64,true),(85,false)]
theorem der_27947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27947 :=
  CNF.rup_sound cl_27947 [cl_5592,cl_27885] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5592 v h) (hints_cons _ _ _ (der_27885 v h) (by intro d hd; cases hd)))
def cl_27948 : CNF.NClause := [(43,false),(12,false),(64,false),(72,true),(68,false),(85,false),(91,true)]
theorem der_27948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27948 :=
  CNF.rup_sound cl_27948 [cl_5593,cl_27936] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5593 v h) (hints_cons _ _ _ (der_27936 v h) (by intro d hd; cases hd)))
def cl_27949 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(72,true),(64,false),(85,false)]
theorem der_27949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27949 :=
  CNF.rup_sound cl_27949 [cl_5594,cl_27887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5594 v h) (hints_cons _ _ _ (der_27887 v h) (by intro d hd; cases hd)))
def cl_27950 : CNF.NClause := [(43,false),(81,true),(12,false),(64,true),(68,false),(72,true),(85,false)]
theorem der_27950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27950 :=
  CNF.rup_sound cl_27950 [cl_5595,cl_27889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5595 v h) (hints_cons _ _ _ (der_27889 v h) (by intro d hd; cases hd)))
def cl_27951 : CNF.NClause := [(43,false),(81,true),(12,true),(64,true),(72,true),(68,false),(85,false)]
theorem der_27951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27951 :=
  CNF.rup_sound cl_27951 [cl_5596,cl_27889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5596 v h) (hints_cons _ _ _ (der_27889 v h) (by intro d hd; cases hd)))
def cl_27952 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(64,false),(72,true),(85,false)]
theorem der_27952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27952 :=
  CNF.rup_sound cl_27952 [cl_5597,cl_27891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5597 v h) (hints_cons _ _ _ (der_27891 v h) (by intro d hd; cases hd)))
def cl_27953 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(64,false),(72,true),(85,false)]
theorem der_27953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27953 :=
  CNF.rup_sound cl_27953 [cl_5598,cl_27891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5598 v h) (hints_cons _ _ _ (der_27891 v h) (by intro d hd; cases hd)))
def cl_27954 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(64,true),(72,true),(85,false)]
theorem der_27954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27954 :=
  CNF.rup_sound cl_27954 [cl_5599,cl_27892] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5599 v h) (hints_cons _ _ _ (der_27892 v h) (by intro d hd; cases hd)))
def cl_27955 : CNF.NClause := [(43,false),(12,true),(68,true),(64,true),(72,true),(85,false),(91,true)]
theorem der_27955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27955 :=
  CNF.rup_sound cl_27955 [cl_5600,cl_27939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5600 v h) (hints_cons _ _ _ (der_27939 v h) (by intro d hd; cases hd)))
def cl_27956 : CNF.NClause := [(43,false),(12,false),(64,false),(68,false),(81,false),(72,false),(85,true)]
theorem der_27956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27956 :=
  CNF.rup_sound cl_27956 [cl_5601,cl_5537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5601 v h) (hints_cons _ _ _ (inp_5537 v h) (by intro d hd; cases hd)))
def cl_27957 : CNF.NClause := [(43,false),(12,true),(91,true),(72,false),(64,false),(68,false),(81,false)]
theorem der_27957 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27957 :=
  CNF.rup_sound cl_27957 [cl_5602,cl_27925] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5602 v h) (hints_cons _ _ _ (der_27925 v h) (by intro d hd; cases hd)))
def cl_27958 : CNF.NClause := [(43,false),(64,true),(12,false),(72,false),(81,false),(68,false),(85,true)]
theorem der_27958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27958 :=
  CNF.rup_sound cl_27958 [cl_5603,cl_27911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5603 v h) (hints_cons _ _ _ (der_27911 v h) (by intro d hd; cases hd)))
def cl_27959 : CNF.NClause := [(43,false),(12,true),(91,true),(81,false),(68,false),(64,true),(72,false)]
theorem der_27959 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27959 :=
  CNF.rup_sound cl_27959 [cl_5604,cl_27927] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5604 v h) (hints_cons _ _ _ (der_27927 v h) (by intro d hd; cases hd)))
def cl_27960 : CNF.NClause := [(43,false),(85,true),(12,false),(64,false),(72,false),(81,false),(91,true)]
theorem der_27960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27960 :=
  CNF.rup_sound cl_27960 [cl_5605,cl_27956] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5605 v h) (hints_cons _ _ _ (der_27956 v h) (by intro d hd; cases hd)))
def cl_27961 : CNF.NClause := [(43,false),(85,true),(68,true),(64,false),(72,false),(81,false),(91,true)]
theorem der_27961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27961 :=
  CNF.rup_sound cl_27961 [cl_5606,cl_27960] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5606 v h) (hints_cons _ _ _ (der_27960 v h) (by intro d hd; cases hd)))
def cl_27962 : CNF.NClause := [(43,false),(85,true),(12,false),(68,true),(72,false),(81,false),(64,true)]
theorem der_27962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27962 :=
  CNF.rup_sound cl_27962 [cl_5607,cl_27899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5607 v h) (hints_cons _ _ _ (der_27899 v h) (by intro d hd; cases hd)))
def cl_27963 : CNF.NClause := [(43,false),(12,true),(68,true),(72,false),(81,false),(64,true),(91,true)]
theorem der_27963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27963 :=
  CNF.rup_sound cl_27963 [cl_5608,cl_27931] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5608 v h) (hints_cons _ _ _ (der_27931 v h) (by intro d hd; cases hd)))
def cl_27964 : CNF.NClause := [(43,false),(72,true),(12,false),(81,false),(68,false),(64,false),(85,true)]
theorem der_27964 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27964 :=
  CNF.rup_sound cl_27964 [cl_5609,cl_27901] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5609 v h) (hints_cons _ _ _ (der_27901 v h) (by intro d hd; cases hd)))
def cl_27965 : CNF.NClause := [(43,false),(12,true),(68,false),(64,false),(81,false),(85,true),(91,true)]
theorem der_27965 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27965 :=
  CNF.rup_sound cl_27965 [cl_5610,cl_27957] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5610 v h) (hints_cons _ _ _ (der_27957 v h) (by intro d hd; cases hd)))
def cl_27967 : CNF.NClause := [(43,false),(72,true),(12,true),(68,false),(64,true),(81,false),(85,true)]
theorem der_27967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27967 :=
  CNF.rup_sound cl_27967 [cl_5612,cl_27904] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5612 v h) (hints_cons _ _ _ (der_27904 v h) (by intro d hd; cases hd)))
def cl_27968 : CNF.NClause := [(43,false),(72,true),(12,false),(64,false),(81,false),(85,true),(91,true)]
theorem der_27968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27968 :=
  CNF.rup_sound cl_27968 [cl_5613,cl_27964] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5613 v h) (hints_cons _ _ _ (der_27964 v h) (by intro d hd; cases hd)))
def cl_27969 : CNF.NClause := [(43,false),(72,true),(12,true),(68,true),(64,false),(81,false),(85,true)]
theorem der_27969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27969 :=
  CNF.rup_sound cl_27969 [cl_5614,cl_27906] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5614 v h) (hints_cons _ _ _ (der_27906 v h) (by intro d hd; cases hd)))
def cl_27970 : CNF.NClause := [(43,false),(72,true),(12,false),(68,true),(64,true),(81,false),(85,true)]
theorem der_27970 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27970 :=
  CNF.rup_sound cl_27970 [cl_5615,cl_27907] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5615 v h) (hints_cons _ _ _ (der_27907 v h) (by intro d hd; cases hd)))
def cl_27971 : CNF.NClause := [(43,false),(72,true),(12,true),(68,true),(64,true),(81,false),(91,true)]
theorem der_27971 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27971 :=
  CNF.rup_sound cl_27971 [cl_5616,cl_27939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5616 v h) (hints_cons _ _ _ (der_27939 v h) (by intro d hd; cases hd)))
def cl_27972 : CNF.NClause := [(43,false),(81,true),(12,false),(64,false),(72,false),(68,false),(91,true)]
theorem der_27972 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27972 :=
  CNF.rup_sound cl_27972 [cl_5617,cl_27940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5617 v h) (hints_cons _ _ _ (der_27940 v h) (by intro d hd; cases hd)))
def cl_27973 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(72,false),(64,false),(85,true)]
theorem der_27973 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27973 :=
  CNF.rup_sound cl_27973 [cl_5618,cl_27910] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5618 v h) (hints_cons _ _ _ (der_27910 v h) (by intro d hd; cases hd)))
def cl_27974 : CNF.NClause := [(43,false),(12,false),(64,true),(72,false),(68,false),(85,true),(91,true)]
theorem der_27974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27974 :=
  CNF.rup_sound cl_27974 [cl_5619,cl_27958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5619 v h) (hints_cons _ _ _ (der_27958 v h) (by intro d hd; cases hd)))
def cl_27975 : CNF.NClause := [(43,false),(81,true),(12,true),(64,true),(68,false),(72,false),(91,true)]
theorem der_27975 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27975 :=
  CNF.rup_sound cl_27975 [cl_5620,cl_27943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5620 v h) (hints_cons _ _ _ (der_27943 v h) (by intro d hd; cases hd)))
def cl_27976 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(64,false),(72,false),(85,true)]
theorem der_27976 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27976 :=
  CNF.rup_sound cl_27976 [cl_5621,cl_27913] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5621 v h) (hints_cons _ _ _ (der_27913 v h) (by intro d hd; cases hd)))
def cl_27977 : CNF.NClause := [(43,false),(81,true),(12,true),(64,false),(72,false),(85,true),(91,true)]
theorem der_27977 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27977 :=
  CNF.rup_sound cl_27977 [cl_5622,cl_27973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5622 v h) (hints_cons _ _ _ (der_27973 v h) (by intro d hd; cases hd)))
def cl_27978 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(72,false),(64,true),(91,true)]
theorem der_27978 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27978 :=
  CNF.rup_sound cl_27978 [cl_5623,cl_27946] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5623 v h) (hints_cons _ _ _ (der_27946 v h) (by intro d hd; cases hd)))
def cl_27979 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(72,false),(64,true),(85,true)]
theorem der_27979 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27979 :=
  CNF.rup_sound cl_27979 [cl_5624,cl_27916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5624 v h) (hints_cons _ _ _ (der_27916 v h) (by intro d hd; cases hd)))
def cl_27981 : CNF.NClause := [(43,false),(81,true),(12,true),(68,false),(64,false),(85,true),(91,true)]
theorem der_27981 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27981 :=
  CNF.rup_sound cl_27981 [cl_5626,cl_27973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5626 v h) (hints_cons _ _ _ (der_27973 v h) (by intro d hd; cases hd)))
def cl_27983 : CNF.NClause := [(43,false),(81,true),(12,true),(64,true),(72,true),(68,false),(85,true)]
theorem der_27983 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27983 :=
  CNF.rup_sound cl_27983 [cl_5628,cl_27920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5628 v h) (hints_cons _ _ _ (der_27920 v h) (by intro d hd; cases hd)))
def cl_27984 : CNF.NClause := [(43,false),(81,true),(12,false),(68,true),(64,false),(72,true),(85,true)]
theorem der_27984 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27984 :=
  CNF.rup_sound cl_27984 [cl_5629,cl_27921] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5629 v h) (hints_cons _ _ _ (der_27921 v h) (by intro d hd; cases hd)))
def cl_27985 : CNF.NClause := [(43,false),(81,true),(12,true),(68,true),(64,false),(72,true),(91,true)]
theorem der_27985 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27985 :=
  CNF.rup_sound cl_27985 [cl_5630,cl_27953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5630 v h) (hints_cons _ _ _ (der_27953 v h) (by intro d hd; cases hd)))
def cl_27987 : CNF.NClause := [(43,false),(81,true),(12,true),(64,true),(72,true),(85,true),(91,true)]
theorem der_27987 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27987 :=
  CNF.rup_sound cl_27987 [cl_5632,cl_27983] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5632 v h) (hints_cons _ _ _ (der_27983 v h) (by intro d hd; cases hd)))
def cl_27988 : CNF.NClause := [(33,false),(69,false),(79,false),(84,false),(74,false),(64,true),(87,false)]
theorem der_27988 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27988 :=
  CNF.rup_sound cl_27988 [cl_4227,cl_26323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4227 v h) (hints_cons _ _ _ (der_26323 v h) (by intro d hd; cases hd)))
def cl_27989 : CNF.NClause := [(33,false),(2,true),(64,false),(74,false),(79,false),(84,false),(87,false)]
theorem der_27989 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27989 :=
  CNF.rup_sound cl_27989 [cl_4230,cl_26323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4230 v h) (hints_cons _ _ _ (der_26323 v h) (by intro d hd; cases hd)))
def cl_27990 : CNF.NClause := [(33,false),(2,false),(64,true),(74,false),(79,false),(84,false),(87,false)]
theorem der_27990 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27990 :=
  CNF.rup_sound cl_27990 [cl_4231,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4231 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_27991 : CNF.NClause := [(33,false),(2,true),(64,true),(74,false),(79,false),(84,false),(87,false)]
theorem der_27991 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27991 :=
  CNF.rup_sound cl_27991 [cl_4232,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4232 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_27992 : CNF.NClause := [(33,false),(74,true),(79,false),(69,false),(84,false),(64,false),(87,false)]
theorem der_27992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27992 :=
  CNF.rup_sound cl_27992 [cl_4234,cl_4233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4234 v h) (hints_cons _ _ _ (inp_4233 v h) (by intro d hd; cases hd)))
def cl_27993 : CNF.NClause := [(33,false),(2,false),(69,false),(64,true),(79,false),(84,false),(87,false)]
theorem der_27993 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27993 :=
  CNF.rup_sound cl_27993 [cl_4235,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4235 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_27994 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(79,false),(84,false),(87,false)]
theorem der_27994 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27994 :=
  CNF.rup_sound cl_27994 [cl_4236,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4236 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_27995 : CNF.NClause := [(33,false),(2,false),(64,false),(74,true),(79,false),(84,false),(87,false)]
theorem der_27995 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27995 :=
  CNF.rup_sound cl_27995 [cl_4237,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4237 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_27996 : CNF.NClause := [(33,false),(2,true),(64,false),(74,true),(79,false),(84,false),(87,false)]
theorem der_27996 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27996 :=
  CNF.rup_sound cl_27996 [cl_4238,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4238 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_27997 : CNF.NClause := [(33,false),(69,true),(2,false),(74,true),(79,false),(84,false),(87,false)]
theorem der_27997 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27997 :=
  CNF.rup_sound cl_27997 [cl_4239,cl_27995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4239 v h) (hints_cons _ _ _ (der_27995 v h) (by intro d hd; cases hd)))
def cl_27998 : CNF.NClause := [(33,false),(69,true),(64,true),(74,true),(79,false),(84,false),(87,false)]
theorem der_27998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27998 :=
  CNF.rup_sound cl_27998 [cl_4240,cl_27997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4240 v h) (hints_cons _ _ _ (der_27997 v h) (by intro d hd; cases hd)))
def cl_27999 : CNF.NClause := [(33,false),(79,true),(64,false),(74,false),(69,false),(84,false),(87,false)]
theorem der_27999 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_27999 :=
  CNF.rup_sound cl_27999 [cl_4242,cl_4241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4242 v h) (hints_cons _ _ _ (inp_4241 v h) (by intro d hd; cases hd)))
def cl_28000 : CNF.NClause := [(33,false),(2,false),(69,false),(74,false),(64,true),(84,false),(87,false)]
theorem der_28000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28000 :=
  CNF.rup_sound cl_28000 [cl_4243,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4243 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_28001 : CNF.NClause := [(33,false),(2,true),(64,true),(74,false),(69,false),(84,false),(87,false)]
theorem der_28001 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28001 :=
  CNF.rup_sound cl_28001 [cl_4244,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4244 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_28002 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(74,false),(84,false),(87,false)]
theorem der_28002 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28002 :=
  CNF.rup_sound cl_28002 [cl_4245,cl_27999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4245 v h) (hints_cons _ _ _ (der_27999 v h) (by intro d hd; cases hd)))
def cl_28003 : CNF.NClause := [(33,false),(79,true),(2,true),(64,false),(74,false),(84,false),(87,false)]
theorem der_28003 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28003 :=
  CNF.rup_sound cl_28003 [cl_4246,cl_27999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4246 v h) (hints_cons _ _ _ (der_27999 v h) (by intro d hd; cases hd)))
def cl_28004 : CNF.NClause := [(33,false),(69,true),(2,false),(74,false),(79,true),(84,false),(87,false)]
theorem der_28004 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28004 :=
  CNF.rup_sound cl_28004 [cl_4247,cl_28002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4247 v h) (hints_cons _ _ _ (der_28002 v h) (by intro d hd; cases hd)))
def cl_28005 : CNF.NClause := [(33,false),(69,true),(64,true),(74,false),(79,true),(84,false),(87,false)]
theorem der_28005 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28005 :=
  CNF.rup_sound cl_28005 [cl_4248,cl_28004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4248 v h) (hints_cons _ _ _ (der_28004 v h) (by intro d hd; cases hd)))
def cl_28006 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(84,false),(87,false)]
theorem der_28006 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28006 :=
  CNF.rup_sound cl_28006 [cl_4249,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4249 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_28007 : CNF.NClause := [(33,false),(2,true),(64,false),(69,false),(74,true),(84,false),(87,false)]
theorem der_28007 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28007 :=
  CNF.rup_sound cl_28007 [cl_4250,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4250 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_28008 : CNF.NClause := [(33,false),(74,true),(2,false),(69,false),(64,true),(84,false),(87,false)]
theorem der_28008 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28008 :=
  CNF.rup_sound cl_28008 [cl_4251,cl_27993] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4251 v h) (hints_cons _ _ _ (der_27993 v h) (by intro d hd; cases hd)))
def cl_28009 : CNF.NClause := [(33,false),(79,true),(64,true),(69,false),(74,true),(84,false),(87,false)]
theorem der_28009 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28009 :=
  CNF.rup_sound cl_28009 [cl_4252,cl_28008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4252 v h) (hints_cons _ _ _ (der_28008 v h) (by intro d hd; cases hd)))
def cl_28010 : CNF.NClause := [(33,false),(69,true),(2,false),(64,false),(74,true),(84,false),(87,false)]
theorem der_28010 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28010 :=
  CNF.rup_sound cl_28010 [cl_4253,cl_27995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4253 v h) (hints_cons _ _ _ (der_27995 v h) (by intro d hd; cases hd)))
def cl_28011 : CNF.NClause := [(33,false),(69,true),(64,false),(74,true),(79,true),(84,false),(87,false)]
theorem der_28011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28011 :=
  CNF.rup_sound cl_28011 [cl_4254,cl_28010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4254 v h) (hints_cons _ _ _ (der_28010 v h) (by intro d hd; cases hd)))
def cl_28013 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,true),(84,false),(87,false)]
theorem der_28013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28013 :=
  CNF.rup_sound cl_28013 [cl_4256,cl_27998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4256 v h) (hints_cons _ _ _ (der_27998 v h) (by intro d hd; cases hd)))
def cl_28014 : CNF.NClause := [(33,false),(84,true),(64,false),(69,false),(79,false),(74,false),(87,false)]
theorem der_28014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28014 :=
  CNF.rup_sound cl_28014 [cl_4258,cl_4257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4258 v h) (hints_cons _ _ _ (inp_4257 v h) (by intro d hd; cases hd)))
def cl_28015 : CNF.NClause := [(33,false),(2,false),(69,false),(74,false),(64,true),(79,false),(87,false)]
theorem der_28015 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28015 :=
  CNF.rup_sound cl_28015 [cl_4259,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4259 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_28016 : CNF.NClause := [(33,false),(2,true),(87,false),(74,false),(64,true),(69,false),(79,false)]
theorem der_28016 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28016 :=
  CNF.rup_sound cl_28016 [cl_4260,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4260 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_28017 : CNF.NClause := [(33,false),(2,false),(64,false),(74,false),(79,false),(84,true),(87,false)]
theorem der_28017 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28017 :=
  CNF.rup_sound cl_28017 [cl_4261,cl_4257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4261 v h) (hints_cons _ _ _ (inp_4257 v h) (by intro d hd; cases hd)))
def cl_28018 : CNF.NClause := [(33,false),(69,true),(64,false),(74,false),(79,false),(84,true),(87,false)]
theorem der_28018 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28018 :=
  CNF.rup_sound cl_28018 [cl_4262,cl_28017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4262 v h) (hints_cons _ _ _ (der_28017 v h) (by intro d hd; cases hd)))
def cl_28019 : CNF.NClause := [(33,false),(69,true),(2,false),(74,false),(79,false),(84,true),(87,false)]
theorem der_28019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28019 :=
  CNF.rup_sound cl_28019 [cl_4263,cl_28017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4263 v h) (hints_cons _ _ _ (der_28017 v h) (by intro d hd; cases hd)))
def cl_28020 : CNF.NClause := [(33,false),(69,true),(64,true),(74,false),(79,false),(84,true),(87,false)]
theorem der_28020 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28020 :=
  CNF.rup_sound cl_28020 [cl_4264,cl_28019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4264 v h) (hints_cons _ _ _ (der_28019 v h) (by intro d hd; cases hd)))
def cl_28021 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(79,false),(74,true),(87,false)]
theorem der_28021 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28021 :=
  CNF.rup_sound cl_28021 [cl_4265,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4265 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_28022 : CNF.NClause := [(33,false),(2,true),(79,false),(64,false),(87,false),(69,false),(74,true)]
theorem der_28022 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28022 :=
  CNF.rup_sound cl_28022 [cl_4266,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4266 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_28023 : CNF.NClause := [(33,false),(74,true),(2,false),(69,false),(64,true),(79,false),(87,false)]
theorem der_28023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28023 :=
  CNF.rup_sound cl_28023 [cl_4267,cl_28008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4267 v h) (hints_cons _ _ _ (der_28008 v h) (by intro d hd; cases hd)))
def cl_28024 : CNF.NClause := [(33,false),(84,true),(74,true),(69,false),(79,false),(64,true),(87,false)]
theorem der_28024 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28024 :=
  CNF.rup_sound cl_28024 [cl_4268,cl_28023] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4268 v h) (hints_cons _ _ _ (der_28023 v h) (by intro d hd; cases hd)))
def cl_28025 : CNF.NClause := [(33,false),(69,true),(2,false),(64,false),(74,true),(79,false),(87,false)]
theorem der_28025 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28025 :=
  CNF.rup_sound cl_28025 [cl_4269,cl_27995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4269 v h) (hints_cons _ _ _ (der_27995 v h) (by intro d hd; cases hd)))
def cl_28026 : CNF.NClause := [(33,false),(69,true),(2,true),(64,false),(74,true),(79,false),(87,false)]
theorem der_28026 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28026 :=
  CNF.rup_sound cl_28026 [cl_4270,cl_27996] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4270 v h) (hints_cons _ _ _ (der_27996 v h) (by intro d hd; cases hd)))
def cl_28027 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,true),(79,false),(87,false)]
theorem der_28027 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28027 :=
  CNF.rup_sound cl_28027 [cl_4271,cl_27998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4271 v h) (hints_cons _ _ _ (der_27998 v h) (by intro d hd; cases hd)))
def cl_28028 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,true),(79,false),(87,false)]
theorem der_28028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28028 :=
  CNF.rup_sound cl_28028 [cl_4272,cl_27998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4272 v h) (hints_cons _ _ _ (der_27998 v h) (by intro d hd; cases hd)))
def cl_28029 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(69,false),(74,false),(87,false)]
theorem der_28029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28029 :=
  CNF.rup_sound cl_28029 [cl_4273,cl_27999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4273 v h) (hints_cons _ _ _ (der_27999 v h) (by intro d hd; cases hd)))
def cl_28030 : CNF.NClause := [(33,false),(79,true),(2,true),(74,false),(64,false),(69,false),(87,false)]
theorem der_28030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28030 :=
  CNF.rup_sound cl_28030 [cl_4274,cl_27999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4274 v h) (hints_cons _ _ _ (der_27999 v h) (by intro d hd; cases hd)))
def cl_28031 : CNF.NClause := [(33,false),(79,true),(2,false),(69,false),(74,false),(64,true),(87,false)]
theorem der_28031 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28031 :=
  CNF.rup_sound cl_28031 [cl_4275,cl_28000] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4275 v h) (hints_cons _ _ _ (der_28000 v h) (by intro d hd; cases hd)))
def cl_28032 : CNF.NClause := [(33,false),(79,true),(84,true),(74,false),(64,true),(69,false),(87,false)]
theorem der_28032 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28032 :=
  CNF.rup_sound cl_28032 [cl_4276,cl_28031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4276 v h) (hints_cons _ _ _ (der_28031 v h) (by intro d hd; cases hd)))
def cl_28033 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(74,false),(69,true),(87,false)]
theorem der_28033 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28033 :=
  CNF.rup_sound cl_28033 [cl_4277,cl_28002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4277 v h) (hints_cons _ _ _ (der_28002 v h) (by intro d hd; cases hd)))
def cl_28034 : CNF.NClause := [(33,false),(79,true),(64,false),(74,false),(69,true),(84,true),(87,false)]
theorem der_28034 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28034 :=
  CNF.rup_sound cl_28034 [cl_4278,cl_28033] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4278 v h) (hints_cons _ _ _ (der_28033 v h) (by intro d hd; cases hd)))
def cl_28035 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,false),(79,true),(87,false)]
theorem der_28035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28035 :=
  CNF.rup_sound cl_28035 [cl_4279,cl_28005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4279 v h) (hints_cons _ _ _ (der_28005 v h) (by intro d hd; cases hd)))
def cl_28036 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,false),(79,true),(87,false)]
theorem der_28036 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28036 :=
  CNF.rup_sound cl_28036 [cl_4280,cl_28005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4280 v h) (hints_cons _ _ _ (der_28005 v h) (by intro d hd; cases hd)))
def cl_28037 : CNF.NClause := [(33,false),(2,false),(64,false),(69,false),(74,true),(84,true),(87,false)]
theorem der_28037 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28037 :=
  CNF.rup_sound cl_28037 [cl_4281,cl_28021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4281 v h) (hints_cons _ _ _ (der_28021 v h) (by intro d hd; cases hd)))
def cl_28038 : CNF.NClause := [(33,false),(79,true),(2,true),(64,false),(69,false),(74,true),(87,false)]
theorem der_28038 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28038 :=
  CNF.rup_sound cl_28038 [cl_4282,cl_28007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4282 v h) (hints_cons _ _ _ (der_28007 v h) (by intro d hd; cases hd)))
def cl_28039 : CNF.NClause := [(33,false),(74,true),(2,false),(69,false),(64,true),(79,true),(87,false)]
theorem der_28039 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28039 :=
  CNF.rup_sound cl_28039 [cl_4283,cl_28008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4283 v h) (hints_cons _ _ _ (der_28008 v h) (by intro d hd; cases hd)))
def cl_28040 : CNF.NClause := [(33,false),(79,true),(2,true),(64,true),(69,false),(74,true),(87,false)]
theorem der_28040 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28040 :=
  CNF.rup_sound cl_28040 [cl_4284,cl_28009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4284 v h) (hints_cons _ _ _ (der_28009 v h) (by intro d hd; cases hd)))
def cl_28041 : CNF.NClause := [(33,false),(69,true),(2,false),(64,false),(74,true),(79,true),(87,false)]
theorem der_28041 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28041 :=
  CNF.rup_sound cl_28041 [cl_4285,cl_28010] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4285 v h) (hints_cons _ _ _ (der_28010 v h) (by intro d hd; cases hd)))
def cl_28042 : CNF.NClause := [(33,false),(69,true),(64,false),(74,true),(79,true),(84,true),(87,false)]
theorem der_28042 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28042 :=
  CNF.rup_sound cl_28042 [cl_4286,cl_28041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4286 v h) (hints_cons _ _ _ (der_28041 v h) (by intro d hd; cases hd)))
def cl_28043 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,true),(84,true),(87,false)]
theorem der_28043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28043 :=
  CNF.rup_sound cl_28043 [cl_4287,cl_28027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4287 v h) (hints_cons _ _ _ (der_28027 v h) (by intro d hd; cases hd)))
def cl_28044 : CNF.NClause := [(33,false),(69,true),(64,true),(74,true),(79,true),(84,true),(87,false)]
theorem der_28044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28044 :=
  CNF.rup_sound cl_28044 [cl_4288,cl_28043] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4288 v h) (hints_cons _ _ _ (der_28043 v h) (by intro d hd; cases hd)))
def cl_28045 : CNF.NClause := [(33,false),(79,false),(2,true),(74,false),(69,false),(87,true),(84,false)]
theorem der_28045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28045 :=
  CNF.rup_sound cl_28045 [cl_4290,cl_26322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4290 v h) (hints_cons _ _ _ (der_26322 v h) (by intro d hd; cases hd)))
def cl_28046 : CNF.NClause := [(33,false),(84,false),(2,false),(69,false),(74,false),(64,true),(79,false)]
theorem der_28046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28046 :=
  CNF.rup_sound cl_28046 [cl_4291,cl_27988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4291 v h) (hints_cons _ _ _ (der_27988 v h) (by intro d hd; cases hd)))
def cl_28047 : CNF.NClause := [(33,false),(69,true),(2,false),(64,false),(74,false),(79,false),(84,false)]
theorem der_28047 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28047 :=
  CNF.rup_sound cl_28047 [cl_4293,cl_4229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4293 v h) (hints_cons _ _ _ (inp_4229 v h) (by intro d hd; cases hd)))
def cl_28048 : CNF.NClause := [(33,false),(69,true),(2,true),(64,false),(74,false),(79,false),(84,false)]
theorem der_28048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28048 :=
  CNF.rup_sound cl_28048 [cl_4294,cl_27989] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4294 v h) (hints_cons _ _ _ (der_27989 v h) (by intro d hd; cases hd)))
def cl_28049 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,false),(79,false),(84,false)]
theorem der_28049 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28049 :=
  CNF.rup_sound cl_28049 [cl_4295,cl_27990] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4295 v h) (hints_cons _ _ _ (der_27990 v h) (by intro d hd; cases hd)))
def cl_28050 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,false),(79,false),(84,false)]
theorem der_28050 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28050 :=
  CNF.rup_sound cl_28050 [cl_4296,cl_27991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4296 v h) (hints_cons _ _ _ (der_27991 v h) (by intro d hd; cases hd)))
def cl_28051 : CNF.NClause := [(33,false),(74,true),(2,false),(64,false),(69,false),(79,false),(84,false)]
theorem der_28051 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28051 :=
  CNF.rup_sound cl_28051 [cl_4297,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4297 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_28052 : CNF.NClause := [(33,false),(2,true),(74,true),(69,false),(79,false),(84,false),(64,false)]
theorem der_28052 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28052 :=
  CNF.rup_sound cl_28052 [cl_4298,cl_27992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4298 v h) (hints_cons _ _ _ (der_27992 v h) (by intro d hd; cases hd)))
def cl_28053 : CNF.NClause := [(33,false),(74,true),(2,false),(69,false),(64,true),(79,false),(84,false)]
theorem der_28053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28053 :=
  CNF.rup_sound cl_28053 [cl_4299,cl_28008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4299 v h) (hints_cons _ _ _ (der_28008 v h) (by intro d hd; cases hd)))
def cl_28054 : CNF.NClause := [(33,false),(64,true),(2,true),(74,true),(69,false),(79,false),(84,false)]
theorem der_28054 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28054 :=
  CNF.rup_sound cl_28054 [cl_4300,cl_27994] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4300 v h) (hints_cons _ _ _ (der_27994 v h) (by intro d hd; cases hd)))
def cl_28055 : CNF.NClause := [(33,false),(69,true),(2,false),(64,false),(74,true),(79,false),(84,false)]
theorem der_28055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28055 :=
  CNF.rup_sound cl_28055 [cl_4301,cl_27995] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4301 v h) (hints_cons _ _ _ (der_27995 v h) (by intro d hd; cases hd)))
def cl_28056 : CNF.NClause := [(33,false),(69,true),(64,false),(74,true),(79,false),(84,false),(87,true)]
theorem der_28056 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28056 :=
  CNF.rup_sound cl_28056 [cl_4302,cl_28055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4302 v h) (hints_cons _ _ _ (der_28055 v h) (by intro d hd; cases hd)))
def cl_28058 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,true),(79,false),(84,false)]
theorem der_28058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28058 :=
  CNF.rup_sound cl_28058 [cl_4304,cl_27998] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4304 v h) (hints_cons _ _ _ (der_27998 v h) (by intro d hd; cases hd)))
def cl_28059 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(69,false),(74,false),(84,false)]
theorem der_28059 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28059 :=
  CNF.rup_sound cl_28059 [cl_4305,cl_27999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4305 v h) (hints_cons _ _ _ (der_27999 v h) (by intro d hd; cases hd)))
def cl_28060 : CNF.NClause := [(33,false),(79,true),(2,true),(64,false),(74,false),(69,false),(84,false)]
theorem der_28060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28060 :=
  CNF.rup_sound cl_28060 [cl_4306,cl_27999] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4306 v h) (hints_cons _ _ _ (der_27999 v h) (by intro d hd; cases hd)))
def cl_28061 : CNF.NClause := [(33,false),(79,true),(2,false),(69,false),(74,false),(64,true),(84,false)]
theorem der_28061 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28061 :=
  CNF.rup_sound cl_28061 [cl_4307,cl_28031] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4307 v h) (hints_cons _ _ _ (der_28031 v h) (by intro d hd; cases hd)))
def cl_28062 : CNF.NClause := [(33,false),(2,true),(64,true),(69,false),(74,false),(84,false),(87,true)]
theorem der_28062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28062 :=
  CNF.rup_sound cl_28062 [cl_4308,cl_26322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4308 v h) (hints_cons _ _ _ (der_26322 v h) (by intro d hd; cases hd)))
def cl_28063 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(74,false),(69,true),(84,false)]
theorem der_28063 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28063 :=
  CNF.rup_sound cl_28063 [cl_4309,cl_28002] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4309 v h) (hints_cons _ _ _ (der_28002 v h) (by intro d hd; cases hd)))
def cl_28064 : CNF.NClause := [(33,false),(79,true),(64,false),(74,false),(69,true),(84,false),(87,true)]
theorem der_28064 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28064 :=
  CNF.rup_sound cl_28064 [cl_4310,cl_28063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4310 v h) (hints_cons _ _ _ (der_28063 v h) (by intro d hd; cases hd)))
def cl_28065 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,false),(79,true),(84,false)]
theorem der_28065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28065 :=
  CNF.rup_sound cl_28065 [cl_4311,cl_28005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4311 v h) (hints_cons _ _ _ (der_28005 v h) (by intro d hd; cases hd)))
def cl_28066 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,false),(79,true),(84,false)]
theorem der_28066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28066 :=
  CNF.rup_sound cl_28066 [cl_4312,cl_28005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4312 v h) (hints_cons _ _ _ (der_28005 v h) (by intro d hd; cases hd)))
def cl_28067 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(69,false),(84,false),(87,true)]
theorem der_28067 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28067 :=
  CNF.rup_sound cl_28067 [cl_4313,cl_28059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4313 v h) (hints_cons _ _ _ (der_28059 v h) (by intro d hd; cases hd)))
def cl_28068 : CNF.NClause := [(33,false),(79,true),(64,false),(69,false),(74,true),(84,false),(87,true)]
theorem der_28068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28068 :=
  CNF.rup_sound cl_28068 [cl_4314,cl_28067] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4314 v h) (hints_cons _ _ _ (der_28067 v h) (by intro d hd; cases hd)))
def cl_28069 : CNF.NClause := [(33,false),(74,true),(2,false),(69,false),(64,true),(79,true),(84,false)]
theorem der_28069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28069 :=
  CNF.rup_sound cl_28069 [cl_4315,cl_28008] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4315 v h) (hints_cons _ _ _ (der_28008 v h) (by intro d hd; cases hd)))
def cl_28070 : CNF.NClause := [(33,false),(79,true),(2,true),(64,true),(69,false),(74,true),(84,false)]
theorem der_28070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28070 :=
  CNF.rup_sound cl_28070 [cl_4316,cl_28009] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4316 v h) (hints_cons _ _ _ (der_28009 v h) (by intro d hd; cases hd)))
def cl_28072 : CNF.NClause := [(33,false),(2,true),(64,false),(74,true),(79,true),(84,false),(87,true)]
theorem der_28072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28072 :=
  CNF.rup_sound cl_28072 [cl_4318,cl_28068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4318 v h) (hints_cons _ _ _ (der_28068 v h) (by intro d hd; cases hd)))
def cl_28074 : CNF.NClause := [(33,false),(69,true),(2,true),(74,true),(79,true),(84,false),(87,true)]
theorem der_28074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28074 :=
  CNF.rup_sound cl_28074 [cl_4320,cl_28072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4320 v h) (hints_cons _ _ _ (der_28072 v h) (by intro d hd; cases hd)))
def cl_28075 : CNF.NClause := [(33,false),(84,true),(2,false),(64,false),(69,false),(79,false),(74,false)]
theorem der_28075 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28075 :=
  CNF.rup_sound cl_28075 [cl_4321,cl_4257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4321 v h) (hints_cons _ _ _ (inp_4257 v h) (by intro d hd; cases hd)))
def cl_28076 : CNF.NClause := [(33,false),(84,true),(64,false),(74,false),(79,false),(69,false),(87,true)]
theorem der_28076 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28076 :=
  CNF.rup_sound cl_28076 [cl_4322,cl_28075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4322 v h) (hints_cons _ _ _ (der_28075 v h) (by intro d hd; cases hd)))
def cl_28077 : CNF.NClause := [(33,false),(2,false),(69,false),(74,false),(64,true),(79,false),(87,true)]
theorem der_28077 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28077 :=
  CNF.rup_sound cl_28077 [cl_4323,cl_28046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4323 v h) (hints_cons _ _ _ (der_28046 v h) (by intro d hd; cases hd)))
def cl_28078 : CNF.NClause := [(33,false),(64,true),(2,true),(84,true),(74,false),(79,false),(69,false)]
theorem der_28078 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28078 :=
  CNF.rup_sound cl_28078 [cl_4324,cl_28016] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4324 v h) (hints_cons _ _ _ (der_28016 v h) (by intro d hd; cases hd)))
def cl_28079 : CNF.NClause := [(33,false),(69,true),(2,false),(64,false),(74,false),(79,false),(84,true)]
theorem der_28079 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28079 :=
  CNF.rup_sound cl_28079 [cl_4325,cl_28017] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4325 v h) (hints_cons _ _ _ (der_28017 v h) (by intro d hd; cases hd)))
def cl_28080 : CNF.NClause := [(33,false),(69,true),(64,false),(74,false),(79,false),(84,true),(87,true)]
theorem der_28080 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28080 :=
  CNF.rup_sound cl_28080 [cl_4326,cl_28079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4326 v h) (hints_cons _ _ _ (der_28079 v h) (by intro d hd; cases hd)))
def cl_28081 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,false),(79,false),(84,true)]
theorem der_28081 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28081 :=
  CNF.rup_sound cl_28081 [cl_4327,cl_28019] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4327 v h) (hints_cons _ _ _ (der_28019 v h) (by intro d hd; cases hd)))
def cl_28082 : CNF.NClause := [(33,false),(69,true),(2,true),(74,false),(79,false),(84,true),(87,true)]
theorem der_28082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28082 :=
  CNF.rup_sound cl_28082 [cl_4328,cl_28080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4328 v h) (hints_cons _ _ _ (der_28080 v h) (by intro d hd; cases hd)))
def cl_28083 : CNF.NClause := [(33,false),(84,true),(2,false),(64,false),(69,false),(79,false),(74,true)]
theorem der_28083 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28083 :=
  CNF.rup_sound cl_28083 [cl_4329,cl_28021] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4329 v h) (hints_cons _ _ _ (der_28021 v h) (by intro d hd; cases hd)))
def cl_28084 : CNF.NClause := [(33,false),(84,true),(2,true),(64,false),(69,false),(79,false),(87,true)]
theorem der_28084 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28084 :=
  CNF.rup_sound cl_28084 [cl_4330,cl_28076] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4330 v h) (hints_cons _ _ _ (der_28076 v h) (by intro d hd; cases hd)))
def cl_28085 : CNF.NClause := [(33,false),(2,false),(69,false),(64,true),(79,false),(84,true),(87,true)]
theorem der_28085 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28085 :=
  CNF.rup_sound cl_28085 [cl_4331,cl_28077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4331 v h) (hints_cons _ _ _ (der_28077 v h) (by intro d hd; cases hd)))
def cl_28086 : CNF.NClause := [(33,false),(84,true),(64,true),(69,false),(79,false),(74,true),(87,true)]
theorem der_28086 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28086 :=
  CNF.rup_sound cl_28086 [cl_4332,cl_28085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4332 v h) (hints_cons _ _ _ (der_28085 v h) (by intro d hd; cases hd)))
def cl_28087 : CNF.NClause := [(33,false),(2,false),(64,false),(74,true),(79,false),(84,true),(87,true)]
theorem der_28087 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28087 :=
  CNF.rup_sound cl_28087 [cl_4333,cl_28083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4333 v h) (hints_cons _ _ _ (der_28083 v h) (by intro d hd; cases hd)))
def cl_28088 : CNF.NClause := [(33,false),(69,true),(64,false),(74,true),(79,false),(84,true),(87,true)]
theorem der_28088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28088 :=
  CNF.rup_sound cl_28088 [cl_4334,cl_28087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4334 v h) (hints_cons _ _ _ (der_28087 v h) (by intro d hd; cases hd)))
def cl_28089 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,true),(79,false),(84,true)]
theorem der_28089 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28089 :=
  CNF.rup_sound cl_28089 [cl_4335,cl_28027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4335 v h) (hints_cons _ _ _ (der_28027 v h) (by intro d hd; cases hd)))
def cl_28090 : CNF.NClause := [(33,false),(69,true),(2,true),(74,true),(79,false),(84,true),(87,true)]
theorem der_28090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28090 :=
  CNF.rup_sound cl_28090 [cl_4336,cl_28088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4336 v h) (hints_cons _ _ _ (der_28088 v h) (by intro d hd; cases hd)))
def cl_28091 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(69,false),(74,false),(87,true)]
theorem der_28091 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28091 :=
  CNF.rup_sound cl_28091 [cl_4337,cl_28059] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4337 v h) (hints_cons _ _ _ (der_28059 v h) (by intro d hd; cases hd)))
def cl_28092 : CNF.NClause := [(33,false),(79,true),(64,false),(69,false),(74,false),(84,true),(87,true)]
theorem der_28092 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28092 :=
  CNF.rup_sound cl_28092 [cl_4338,cl_28091] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4338 v h) (hints_cons _ _ _ (der_28091 v h) (by intro d hd; cases hd)))
def cl_28093 : CNF.NClause := [(33,false),(2,false),(69,false),(74,false),(64,true),(84,true),(87,true)]
theorem der_28093 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28093 :=
  CNF.rup_sound cl_28093 [cl_4339,cl_28085] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4339 v h) (hints_cons _ _ _ (der_28085 v h) (by intro d hd; cases hd)))
def cl_28094 : CNF.NClause := [(33,false),(2,true),(84,true),(74,false),(64,true),(69,false),(87,true)]
theorem der_28094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28094 :=
  CNF.rup_sound cl_28094 [cl_4340,cl_28078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4340 v h) (hints_cons _ _ _ (der_28078 v h) (by intro d hd; cases hd)))
def cl_28095 : CNF.NClause := [(33,false),(79,true),(2,false),(64,false),(74,false),(69,true),(87,true)]
theorem der_28095 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28095 :=
  CNF.rup_sound cl_28095 [cl_4341,cl_28063] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4341 v h) (hints_cons _ _ _ (der_28063 v h) (by intro d hd; cases hd)))
def cl_28096 : CNF.NClause := [(33,false),(79,true),(2,true),(64,false),(74,false),(69,true),(87,true)]
theorem der_28096 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28096 :=
  CNF.rup_sound cl_28096 [cl_4342,cl_28064] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4342 v h) (hints_cons _ _ _ (der_28064 v h) (by intro d hd; cases hd)))
def cl_28097 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,false),(79,true),(84,true)]
theorem der_28097 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28097 :=
  CNF.rup_sound cl_28097 [cl_4343,cl_28035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4343 v h) (hints_cons _ _ _ (der_28035 v h) (by intro d hd; cases hd)))
def cl_28098 : CNF.NClause := [(33,false),(69,true),(64,true),(74,false),(79,true),(84,true),(87,true)]
theorem der_28098 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28098 :=
  CNF.rup_sound cl_28098 [cl_4344,cl_28097] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4344 v h) (hints_cons _ _ _ (der_28097 v h) (by intro d hd; cases hd)))
def cl_28100 : CNF.NClause := [(33,false),(79,true),(2,true),(64,false),(69,false),(74,true),(87,true)]
theorem der_28100 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28100 :=
  CNF.rup_sound cl_28100 [cl_4346,cl_28072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4346 v h) (hints_cons _ _ _ (der_28072 v h) (by intro d hd; cases hd)))
def cl_28102 : CNF.NClause := [(33,false),(79,true),(2,true),(64,true),(69,false),(74,true),(84,true)]
theorem der_28102 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28102 :=
  CNF.rup_sound cl_28102 [cl_4348,cl_28040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4348 v h) (hints_cons _ _ _ (der_28040 v h) (by intro d hd; cases hd)))
def cl_28104 : CNF.NClause := [(33,false),(69,true),(2,true),(64,false),(74,true),(79,true),(87,true)]
theorem der_28104 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28104 :=
  CNF.rup_sound cl_28104 [cl_4350,cl_28072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4350 v h) (hints_cons _ _ _ (der_28072 v h) (by intro d hd; cases hd)))
def cl_28105 : CNF.NClause := [(33,false),(69,true),(2,false),(64,true),(74,true),(79,true),(84,true)]
theorem der_28105 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28105 :=
  CNF.rup_sound cl_28105 [cl_4351,cl_28044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4351 v h) (hints_cons _ _ _ (der_28044 v h) (by intro d hd; cases hd)))
def cl_28106 : CNF.NClause := [(33,false),(69,true),(2,true),(64,true),(74,true),(79,true),(84,true)]
theorem der_28106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28106 :=
  CNF.rup_sound cl_28106 [cl_4352,cl_28044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4352 v h) (hints_cons _ _ _ (der_28044 v h) (by intro d hd; cases hd)))
def cl_28107 : CNF.NClause := [(38,false),(71,false),(7,true),(80,false),(89,false),(73,false),(82,false)]
theorem der_28107 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28107 :=
  CNF.rup_sound cl_28107 [cl_4868,cl_4866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4868 v h) (hints_cons _ _ _ (inp_4866 v h) (by intro d hd; cases hd)))
def cl_28108 : CNF.NClause := [(38,false),(7,true),(80,false),(64,false),(73,false),(89,false),(82,false)]
theorem der_28108 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28108 :=
  CNF.rup_sound cl_28108 [cl_4870,cl_4866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4870 v h) (hints_cons _ _ _ (inp_4866 v h) (by intro d hd; cases hd)))
def cl_28109 : CNF.NClause := [(38,false),(73,false),(7,false),(64,true),(80,false),(82,false),(89,false)]
theorem der_28109 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28109 :=
  CNF.rup_sound cl_28109 [cl_4871,cl_4867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4871 v h) (hints_cons _ _ _ (inp_4867 v h) (by intro d hd; cases hd)))
def cl_28110 : CNF.NClause := [(38,false),(71,true),(7,true),(80,false),(73,false),(82,false),(89,false)]
theorem der_28110 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28110 :=
  CNF.rup_sound cl_28110 [cl_4872,cl_28108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4872 v h) (hints_cons _ _ _ (der_28108 v h) (by intro d hd; cases hd)))
def cl_28111 : CNF.NClause := [(38,false),(71,false),(7,true),(80,false),(64,false),(89,false),(82,false)]
theorem der_28111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28111 :=
  CNF.rup_sound cl_28111 [cl_4874,cl_4866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4874 v h) (hints_cons _ _ _ (inp_4866 v h) (by intro d hd; cases hd)))
def cl_28112 : CNF.NClause := [(38,false),(80,false),(7,false),(71,false),(73,true),(82,false),(89,false)]
theorem der_28112 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28112 :=
  CNF.rup_sound cl_28112 [cl_4875,cl_4873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4875 v h) (hints_cons _ _ _ (inp_4873 v h) (by intro d hd; cases hd)))
def cl_28113 : CNF.NClause := [(38,false),(7,true),(80,false),(71,false),(64,true),(82,false),(89,false)]
theorem der_28113 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28113 :=
  CNF.rup_sound cl_28113 [cl_4876,cl_28107] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4876 v h) (hints_cons _ _ _ (der_28107 v h) (by intro d hd; cases hd)))
def cl_28114 : CNF.NClause := [(38,false),(7,false),(64,false),(73,true),(80,false),(82,false),(89,false)]
theorem der_28114 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28114 :=
  CNF.rup_sound cl_28114 [cl_4877,cl_4873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4877 v h) (hints_cons _ _ _ (inp_4873 v h) (by intro d hd; cases hd)))
def cl_28115 : CNF.NClause := [(38,false),(7,true),(89,false),(73,true),(64,false),(82,false),(80,false)]
theorem der_28115 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28115 :=
  CNF.rup_sound cl_28115 [cl_4878,cl_28111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4878 v h) (hints_cons _ _ _ (der_28111 v h) (by intro d hd; cases hd)))
def cl_28116 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(80,false),(82,false),(89,false)]
theorem der_28116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28116 :=
  CNF.rup_sound cl_28116 [cl_4879,cl_28109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4879 v h) (hints_cons _ _ _ (der_28109 v h) (by intro d hd; cases hd)))
def cl_28117 : CNF.NClause := [(38,false),(73,true),(7,true),(64,true),(80,false),(82,false),(89,false)]
theorem der_28117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28117 :=
  CNF.rup_sound cl_28117 [cl_4880,cl_28113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4880 v h) (hints_cons _ _ _ (der_28113 v h) (by intro d hd; cases hd)))
def cl_28118 : CNF.NClause := [(38,false),(7,true),(89,false),(64,false),(73,false),(71,false),(82,false)]
theorem der_28118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28118 :=
  CNF.rup_sound cl_28118 [cl_4882,cl_28108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4882 v h) (hints_cons _ _ _ (der_28108 v h) (by intro d hd; cases hd)))
def cl_28119 : CNF.NClause := [(38,false),(7,false),(64,true),(73,false),(71,false),(82,false),(89,false)]
theorem der_28119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28119 :=
  CNF.rup_sound cl_28119 [cl_4883,cl_4867] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4883 v h) (hints_cons _ _ _ (inp_4867 v h) (by intro d hd; cases hd)))
def cl_28120 : CNF.NClause := [(38,false),(80,true),(64,true),(89,false),(71,false),(82,false),(73,false)]
theorem der_28120 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28120 :=
  CNF.rup_sound cl_28120 [cl_4884,cl_28119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4884 v h) (hints_cons _ _ _ (der_28119 v h) (by intro d hd; cases hd)))
def cl_28121 : CNF.NClause := [(38,false),(80,true),(7,false),(89,false),(73,false),(82,false),(64,false)]
theorem der_28121 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28121 :=
  CNF.rup_sound cl_28121 [cl_4885,cl_4881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4885 v h) (hints_cons _ _ _ (inp_4881 v h) (by intro d hd; cases hd)))
def cl_28122 : CNF.NClause := [(38,false),(7,true),(64,false),(89,false),(73,false),(82,false),(71,true)]
theorem der_28122 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28122 :=
  CNF.rup_sound cl_28122 [cl_4886,cl_28108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4886 v h) (hints_cons _ _ _ (der_28108 v h) (by intro d hd; cases hd)))
def cl_28123 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(73,false),(82,false),(89,false)]
theorem der_28123 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28123 :=
  CNF.rup_sound cl_28123 [cl_4887,cl_28119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4887 v h) (hints_cons _ _ _ (der_28119 v h) (by intro d hd; cases hd)))
def cl_28124 : CNF.NClause := [(38,false),(80,true),(64,true),(71,true),(73,false),(82,false),(89,false)]
theorem der_28124 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28124 :=
  CNF.rup_sound cl_28124 [cl_4888,cl_28123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4888 v h) (hints_cons _ _ _ (der_28123 v h) (by intro d hd; cases hd)))
def cl_28125 : CNF.NClause := [(38,false),(89,false),(7,false),(64,false),(71,false),(73,true),(82,false)]
theorem der_28125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28125 :=
  CNF.rup_sound cl_28125 [cl_4889,cl_4873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4889 v h) (hints_cons _ _ _ (inp_4873 v h) (by intro d hd; cases hd)))
def cl_28126 : CNF.NClause := [(38,false),(7,true),(71,false),(73,true),(64,false),(82,false),(89,false)]
theorem der_28126 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28126 :=
  CNF.rup_sound cl_28126 [cl_4890,cl_28115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4890 v h) (hints_cons _ _ _ (der_28115 v h) (by intro d hd; cases hd)))
def cl_28127 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(82,false),(89,false)]
theorem der_28127 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28127 :=
  CNF.rup_sound cl_28127 [cl_4891,cl_28112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4891 v h) (hints_cons _ _ _ (der_28112 v h) (by intro d hd; cases hd)))
def cl_28128 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(82,false),(89,false)]
theorem der_28128 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28128 :=
  CNF.rup_sound cl_28128 [cl_4892,cl_28113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4892 v h) (hints_cons _ _ _ (der_28113 v h) (by intro d hd; cases hd)))
def cl_28129 : CNF.NClause := [(38,false),(80,true),(7,false),(64,false),(71,true),(82,false),(89,false)]
theorem der_28129 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28129 :=
  CNF.rup_sound cl_28129 [cl_4893,cl_28121] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4893 v h) (hints_cons _ _ _ (der_28121 v h) (by intro d hd; cases hd)))
def cl_28130 : CNF.NClause := [(38,false),(80,true),(64,false),(73,true),(71,true),(82,false),(89,false)]
theorem der_28130 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28130 :=
  CNF.rup_sound cl_28130 [cl_4894,cl_28129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4894 v h) (hints_cons _ _ _ (der_28129 v h) (by intro d hd; cases hd)))
def cl_28131 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(71,true),(82,false),(89,false)]
theorem der_28131 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28131 :=
  CNF.rup_sound cl_28131 [cl_4895,cl_28123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4895 v h) (hints_cons _ _ _ (der_28123 v h) (by intro d hd; cases hd)))
def cl_28132 : CNF.NClause := [(38,false),(80,true),(7,true),(64,true),(73,true),(82,false),(89,false)]
theorem der_28132 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28132 :=
  CNF.rup_sound cl_28132 [cl_4896,cl_28128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4896 v h) (hints_cons _ _ _ (der_28128 v h) (by intro d hd; cases hd)))
def cl_28133 : CNF.NClause := [(38,false),(7,true),(89,false),(73,false),(80,false),(64,false),(71,false)]
theorem der_28133 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28133 :=
  CNF.rup_sound cl_28133 [cl_4898,cl_28108] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4898 v h) (hints_cons _ _ _ (der_28108 v h) (by intro d hd; cases hd)))
def cl_28134 : CNF.NClause := [(38,false),(7,false),(64,true),(73,false),(80,false),(71,false),(89,false)]
theorem der_28134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28134 :=
  CNF.rup_sound cl_28134 [cl_4899,cl_28119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4899 v h) (hints_cons _ _ _ (der_28119 v h) (by intro d hd; cases hd)))
def cl_28135 : CNF.NClause := [(38,false),(7,true),(71,false),(80,false),(64,true),(89,false),(73,false)]
theorem der_28135 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28135 :=
  CNF.rup_sound cl_28135 [cl_4900,cl_28113] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4900 v h) (hints_cons _ _ _ (der_28113 v h) (by intro d hd; cases hd)))
def cl_28136 : CNF.NClause := [(38,false),(80,false),(7,false),(89,false),(71,true),(73,false),(64,false)]
theorem der_28136 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28136 :=
  CNF.rup_sound cl_28136 [cl_4901,cl_4869] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4901 v h) (hints_cons _ _ _ (inp_4869 v h) (by intro d hd; cases hd)))
def cl_28137 : CNF.NClause := [(38,false),(82,true),(64,false),(89,false),(73,false),(80,false),(71,true)]
theorem der_28137 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28137 :=
  CNF.rup_sound cl_28137 [cl_4902,cl_28136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4902 v h) (hints_cons _ _ _ (der_28136 v h) (by intro d hd; cases hd)))
def cl_28138 : CNF.NClause := [(38,false),(73,false),(7,false),(64,true),(71,true),(80,false),(89,false)]
theorem der_28138 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28138 :=
  CNF.rup_sound cl_28138 [cl_4903,cl_28109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4903 v h) (hints_cons _ _ _ (der_28109 v h) (by intro d hd; cases hd)))
def cl_28139 : CNF.NClause := [(38,false),(73,false),(7,true),(64,true),(80,false),(82,true),(89,false)]
theorem der_28139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28139 :=
  CNF.rup_sound cl_28139 [cl_4904,cl_28135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4904 v h) (hints_cons _ _ _ (der_28135 v h) (by intro d hd; cases hd)))
def cl_28140 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,false),(89,false)]
theorem der_28140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28140 :=
  CNF.rup_sound cl_28140 [cl_4905,cl_4873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4905 v h) (hints_cons _ _ _ (inp_4873 v h) (by intro d hd; cases hd)))
def cl_28141 : CNF.NClause := [(38,false),(7,true),(71,false),(64,false),(73,true),(80,false),(89,false)]
theorem der_28141 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28141 :=
  CNF.rup_sound cl_28141 [cl_4906,cl_28115] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4906 v h) (hints_cons _ _ _ (der_28115 v h) (by intro d hd; cases hd)))
def cl_28142 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(80,false),(89,false)]
theorem der_28142 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28142 :=
  CNF.rup_sound cl_28142 [cl_4907,cl_28112] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4907 v h) (hints_cons _ _ _ (der_28112 v h) (by intro d hd; cases hd)))
def cl_28143 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,false),(89,false)]
theorem der_28143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28143 :=
  CNF.rup_sound cl_28143 [cl_4908,cl_28128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4908 v h) (hints_cons _ _ _ (der_28128 v h) (by intro d hd; cases hd)))
def cl_28144 : CNF.NClause := [(38,false),(82,true),(7,false),(64,false),(80,false),(71,true),(89,false)]
theorem der_28144 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28144 :=
  CNF.rup_sound cl_28144 [cl_4909,cl_28136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4909 v h) (hints_cons _ _ _ (der_28136 v h) (by intro d hd; cases hd)))
def cl_28145 : CNF.NClause := [(38,false),(82,true),(64,false),(73,true),(80,false),(71,true),(89,false)]
theorem der_28145 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28145 :=
  CNF.rup_sound cl_28145 [cl_4910,cl_28144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4910 v h) (hints_cons _ _ _ (der_28144 v h) (by intro d hd; cases hd)))
def cl_28146 : CNF.NClause := [(38,false),(73,true),(7,false),(64,true),(80,false),(82,true),(89,false)]
theorem der_28146 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28146 :=
  CNF.rup_sound cl_28146 [cl_4911,cl_28142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4911 v h) (hints_cons _ _ _ (der_28142 v h) (by intro d hd; cases hd)))
def cl_28147 : CNF.NClause := [(38,false),(73,true),(64,true),(71,true),(80,false),(82,true),(89,false)]
theorem der_28147 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28147 :=
  CNF.rup_sound cl_28147 [cl_4912,cl_28146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4912 v h) (hints_cons _ _ _ (der_28146 v h) (by intro d hd; cases hd)))
def cl_28148 : CNF.NClause := [(38,false),(7,false),(80,true),(71,false),(73,false),(64,false),(89,false)]
theorem der_28148 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28148 :=
  CNF.rup_sound cl_28148 [cl_4913,cl_4881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4913 v h) (hints_cons _ _ _ (inp_4881 v h) (by intro d hd; cases hd)))
def cl_28149 : CNF.NClause := [(38,false),(82,true),(71,false),(89,false),(73,false),(80,true),(64,false)]
theorem der_28149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28149 :=
  CNF.rup_sound cl_28149 [cl_4914,cl_28148] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4914 v h) (hints_cons _ _ _ (der_28148 v h) (by intro d hd; cases hd)))
def cl_28150 : CNF.NClause := [(38,false),(7,false),(64,true),(73,false),(71,false),(80,true),(89,false)]
theorem der_28150 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28150 :=
  CNF.rup_sound cl_28150 [cl_4915,cl_28119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4915 v h) (hints_cons _ _ _ (der_28119 v h) (by intro d hd; cases hd)))
def cl_28151 : CNF.NClause := [(38,false),(7,true),(89,false),(64,true),(71,false),(73,false),(82,true)]
theorem der_28151 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28151 :=
  CNF.rup_sound cl_28151 [cl_4916,cl_28135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4916 v h) (hints_cons _ _ _ (der_28135 v h) (by intro d hd; cases hd)))
def cl_28152 : CNF.NClause := [(38,false),(7,false),(80,true),(71,true),(73,false),(64,false),(89,false)]
theorem der_28152 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28152 :=
  CNF.rup_sound cl_28152 [cl_4917,cl_28129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4917 v h) (hints_cons _ _ _ (der_28129 v h) (by intro d hd; cases hd)))
def cl_28153 : CNF.NClause := [(38,false),(80,true),(7,true),(64,false),(71,true),(73,false),(89,false)]
theorem der_28153 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28153 :=
  CNF.rup_sound cl_28153 [cl_4918,cl_28122] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4918 v h) (hints_cons _ _ _ (der_28122 v h) (by intro d hd; cases hd)))
def cl_28154 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(71,true),(73,false),(89,false)]
theorem der_28154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28154 :=
  CNF.rup_sound cl_28154 [cl_4919,cl_28123] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4919 v h) (hints_cons _ _ _ (der_28123 v h) (by intro d hd; cases hd)))
def cl_28155 : CNF.NClause := [(38,false),(80,true),(64,true),(71,true),(73,false),(82,true),(89,false)]
theorem der_28155 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28155 :=
  CNF.rup_sound cl_28155 [cl_4920,cl_28154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4920 v h) (hints_cons _ _ _ (der_28154 v h) (by intro d hd; cases hd)))
def cl_28156 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(80,true),(89,false)]
theorem der_28156 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28156 :=
  CNF.rup_sound cl_28156 [cl_4921,cl_28125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4921 v h) (hints_cons _ _ _ (der_28125 v h) (by intro d hd; cases hd)))
def cl_28157 : CNF.NClause := [(38,false),(7,true),(71,false),(64,false),(73,true),(80,true),(89,false)]
theorem der_28157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28157 :=
  CNF.rup_sound cl_28157 [cl_4922,cl_28126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4922 v h) (hints_cons _ _ _ (der_28126 v h) (by intro d hd; cases hd)))
def cl_28158 : CNF.NClause := [(38,false),(82,true),(7,false),(64,true),(71,false),(73,true),(89,false)]
theorem der_28158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28158 :=
  CNF.rup_sound cl_28158 [cl_4923,cl_28142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4923 v h) (hints_cons _ _ _ (der_28142 v h) (by intro d hd; cases hd)))
def cl_28159 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,true),(80,true),(89,false)]
theorem der_28159 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28159 :=
  CNF.rup_sound cl_28159 [cl_4924,cl_28128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4924 v h) (hints_cons _ _ _ (der_28128 v h) (by intro d hd; cases hd)))
def cl_28160 : CNF.NClause := [(38,false),(80,true),(7,false),(64,false),(73,true),(71,true),(89,false)]
theorem der_28160 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28160 :=
  CNF.rup_sound cl_28160 [cl_4925,cl_28129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4925 v h) (hints_cons _ _ _ (der_28129 v h) (by intro d hd; cases hd)))
def cl_28161 : CNF.NClause := [(38,false),(80,true),(7,true),(64,false),(71,true),(82,true),(89,false)]
theorem der_28161 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28161 :=
  CNF.rup_sound cl_28161 [cl_4926,cl_28153] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4926 v h) (hints_cons _ _ _ (der_28153 v h) (by intro d hd; cases hd)))
def cl_28162 : CNF.NClause := [(38,false),(7,false),(64,true),(71,true),(73,true),(82,true),(89,false)]
theorem der_28162 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28162 :=
  CNF.rup_sound cl_28162 [cl_4927,cl_28146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4927 v h) (hints_cons _ _ _ (der_28146 v h) (by intro d hd; cases hd)))
def cl_28163 : CNF.NClause := [(38,false),(80,true),(64,true),(71,true),(73,true),(82,true),(89,false)]
theorem der_28163 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28163 :=
  CNF.rup_sound cl_28163 [cl_4928,cl_28162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4928 v h) (hints_cons _ _ _ (der_28162 v h) (by intro d hd; cases hd)))
def cl_28164 : CNF.NClause := [(38,false),(71,false),(7,true),(64,false),(80,false),(73,false),(82,false)]
theorem der_28164 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28164 :=
  CNF.rup_sound cl_28164 [cl_4930,cl_4866] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4930 v h) (hints_cons _ _ _ (inp_4866 v h) (by intro d hd; cases hd)))
def cl_28165 : CNF.NClause := [(38,false),(7,false),(64,true),(73,false),(80,false),(82,false),(71,false)]
theorem der_28165 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28165 :=
  CNF.rup_sound cl_28165 [cl_4931,cl_28119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4931 v h) (hints_cons _ _ _ (der_28119 v h) (by intro d hd; cases hd)))
def cl_28166 : CNF.NClause := [(38,false),(71,false),(7,true),(80,false),(73,false),(82,false),(64,true)]
theorem der_28166 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28166 :=
  CNF.rup_sound cl_28166 [cl_4932,cl_28135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4932 v h) (hints_cons _ _ _ (der_28135 v h) (by intro d hd; cases hd)))
def cl_28167 : CNF.NClause := [(38,false),(80,false),(7,false),(64,false),(73,false),(71,true),(82,false)]
theorem der_28167 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28167 :=
  CNF.rup_sound cl_28167 [cl_4933,cl_28136] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4933 v h) (hints_cons _ _ _ (der_28136 v h) (by intro d hd; cases hd)))
def cl_28168 : CNF.NClause := [(38,false),(7,true),(73,false),(80,false),(64,false),(82,false),(89,true)]
theorem der_28168 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28168 :=
  CNF.rup_sound cl_28168 [cl_4934,cl_28164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4934 v h) (hints_cons _ _ _ (der_28164 v h) (by intro d hd; cases hd)))
def cl_28169 : CNF.NClause := [(38,false),(73,false),(7,false),(64,true),(71,true),(80,false),(82,false)]
theorem der_28169 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28169 :=
  CNF.rup_sound cl_28169 [cl_4935,cl_28109] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4935 v h) (hints_cons _ _ _ (der_28109 v h) (by intro d hd; cases hd)))
def cl_28170 : CNF.NClause := [(38,false),(7,true),(64,true),(73,false),(80,false),(82,false),(89,true)]
theorem der_28170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28170 :=
  CNF.rup_sound cl_28170 [cl_4936,cl_28166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4936 v h) (hints_cons _ _ _ (der_28166 v h) (by intro d hd; cases hd)))
def cl_28171 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,true),(82,false),(80,false)]
theorem der_28171 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28171 :=
  CNF.rup_sound cl_28171 [cl_4937,cl_4873] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4937 v h) (hints_cons _ _ _ (inp_4873 v h) (by intro d hd; cases hd)))
def cl_28172 : CNF.NClause := [(38,false),(71,false),(7,true),(73,true),(64,false),(82,false),(80,false)]
theorem der_28172 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28172 :=
  CNF.rup_sound cl_28172 [cl_4938,cl_28111] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4938 v h) (hints_cons _ _ _ (der_28111 v h) (by intro d hd; cases hd)))
def cl_28173 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(82,false),(80,false)]
theorem der_28173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28173 :=
  CNF.rup_sound cl_28173 [cl_4939,cl_28142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4939 v h) (hints_cons _ _ _ (der_28142 v h) (by intro d hd; cases hd)))
def cl_28174 : CNF.NClause := [(38,false),(73,true),(7,true),(80,false),(71,false),(64,true),(82,false)]
theorem der_28174 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28174 :=
  CNF.rup_sound cl_28174 [cl_4940,cl_28128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4940 v h) (hints_cons _ _ _ (der_28128 v h) (by intro d hd; cases hd)))
def cl_28175 : CNF.NClause := [(38,false),(71,true),(7,false),(64,false),(80,false),(82,false),(89,true)]
theorem der_28175 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28175 :=
  CNF.rup_sound cl_28175 [cl_4941,cl_28167] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4941 v h) (hints_cons _ _ _ (der_28167 v h) (by intro d hd; cases hd)))
def cl_28176 : CNF.NClause := [(38,false),(7,true),(64,false),(73,true),(80,false),(82,false),(89,true)]
theorem der_28176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28176 :=
  CNF.rup_sound cl_28176 [cl_4942,cl_28172] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4942 v h) (hints_cons _ _ _ (der_28172 v h) (by intro d hd; cases hd)))
def cl_28177 : CNF.NClause := [(38,false),(73,true),(7,false),(64,true),(80,false),(82,false),(89,true)]
theorem der_28177 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28177 :=
  CNF.rup_sound cl_28177 [cl_4943,cl_28173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4943 v h) (hints_cons _ _ _ (der_28173 v h) (by intro d hd; cases hd)))
def cl_28178 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(80,false),(82,false),(89,true)]
theorem der_28178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28178 :=
  CNF.rup_sound cl_28178 [cl_4944,cl_28170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4944 v h) (hints_cons _ _ _ (der_28170 v h) (by intro d hd; cases hd)))
def cl_28179 : CNF.NClause := [(38,false),(80,true),(7,false),(64,false),(71,false),(73,false),(82,false)]
theorem der_28179 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28179 :=
  CNF.rup_sound cl_28179 [cl_4945,cl_4881] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4945 v h) (hints_cons _ _ _ (inp_4881 v h) (by intro d hd; cases hd)))
def cl_28180 : CNF.NClause := [(38,false),(7,true),(89,true),(73,false),(64,false),(71,false),(82,false)]
theorem der_28180 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28180 :=
  CNF.rup_sound cl_28180 [cl_4946,cl_28168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4946 v h) (hints_cons _ _ _ (der_28168 v h) (by intro d hd; cases hd)))
def cl_28181 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(73,false),(71,false),(82,false)]
theorem der_28181 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28181 :=
  CNF.rup_sound cl_28181 [cl_4947,cl_28119] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4947 v h) (hints_cons _ _ _ (der_28119 v h) (by intro d hd; cases hd)))
def cl_28182 : CNF.NClause := [(38,false),(7,true),(64,true),(71,false),(73,false),(82,false),(89,true)]
theorem der_28182 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28182 :=
  CNF.rup_sound cl_28182 [cl_4948,cl_28170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4948 v h) (hints_cons _ _ _ (der_28170 v h) (by intro d hd; cases hd)))
def cl_28183 : CNF.NClause := [(38,false),(80,true),(7,false),(64,false),(71,true),(73,false),(82,false)]
theorem der_28183 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28183 :=
  CNF.rup_sound cl_28183 [cl_4949,cl_28129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4949 v h) (hints_cons _ _ _ (der_28129 v h) (by intro d hd; cases hd)))
def cl_28184 : CNF.NClause := [(38,false),(7,true),(64,false),(71,true),(73,false),(82,false),(89,true)]
theorem der_28184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28184 :=
  CNF.rup_sound cl_28184 [cl_4950,cl_28168] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4950 v h) (hints_cons _ _ _ (der_28168 v h) (by intro d hd; cases hd)))
def cl_28185 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(71,true),(73,false),(82,false)]
theorem der_28185 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28185 :=
  CNF.rup_sound cl_28185 [cl_4951,cl_28154] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4951 v h) (hints_cons _ _ _ (der_28154 v h) (by intro d hd; cases hd)))
def cl_28186 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,false),(82,false),(89,true)]
theorem der_28186 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28186 :=
  CNF.rup_sound cl_28186 [cl_4952,cl_28170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4952 v h) (hints_cons _ _ _ (der_28170 v h) (by intro d hd; cases hd)))
def cl_28187 : CNF.NClause := [(38,false),(80,true),(7,false),(64,false),(71,false),(73,true),(82,false)]
theorem der_28187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28187 :=
  CNF.rup_sound cl_28187 [cl_4953,cl_28125] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4953 v h) (hints_cons _ _ _ (der_28125 v h) (by intro d hd; cases hd)))
def cl_28188 : CNF.NClause := [(38,false),(80,true),(7,true),(71,false),(64,false),(73,true),(82,false)]
theorem der_28188 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28188 :=
  CNF.rup_sound cl_28188 [cl_4954,cl_28126] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4954 v h) (hints_cons _ _ _ (der_28126 v h) (by intro d hd; cases hd)))
def cl_28189 : CNF.NClause := [(38,false),(7,false),(64,true),(71,false),(73,true),(82,false),(89,true)]
theorem der_28189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28189 :=
  CNF.rup_sound cl_28189 [cl_4955,cl_28173] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4955 v h) (hints_cons _ _ _ (der_28173 v h) (by intro d hd; cases hd)))
def cl_28190 : CNF.NClause := [(38,false),(80,true),(7,true),(64,true),(71,false),(73,true),(82,false)]
theorem der_28190 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28190 :=
  CNF.rup_sound cl_28190 [cl_4956,cl_28128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4956 v h) (hints_cons _ _ _ (der_28128 v h) (by intro d hd; cases hd)))
def cl_28191 : CNF.NClause := [(38,false),(80,true),(7,false),(64,false),(73,true),(71,true),(82,false)]
theorem der_28191 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28191 :=
  CNF.rup_sound cl_28191 [cl_4957,cl_28129] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4957 v h) (hints_cons _ _ _ (der_28129 v h) (by intro d hd; cases hd)))
def cl_28192 : CNF.NClause := [(38,false),(7,true),(64,false),(73,true),(71,true),(82,false),(89,true)]
theorem der_28192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28192 :=
  CNF.rup_sound cl_28192 [cl_4958,cl_28176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4958 v h) (hints_cons _ _ _ (der_28176 v h) (by intro d hd; cases hd)))
def cl_28193 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(73,true),(82,false),(89,true)]
theorem der_28193 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28193 :=
  CNF.rup_sound cl_28193 [cl_4959,cl_28189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4959 v h) (hints_cons _ _ _ (der_28189 v h) (by intro d hd; cases hd)))
def cl_28194 : CNF.NClause := [(38,false),(7,true),(64,true),(71,true),(73,true),(82,false),(89,true)]
theorem der_28194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28194 :=
  CNF.rup_sound cl_28194 [cl_4960,cl_28178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4960 v h) (hints_cons _ _ _ (der_28178 v h) (by intro d hd; cases hd)))
def cl_28195 : CNF.NClause := [(38,false),(82,true),(7,false),(80,false),(64,false),(71,false),(73,false)]
theorem der_28195 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28195 :=
  CNF.rup_sound cl_28195 [cl_4961,cl_4897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4961 v h) (hints_cons _ _ _ (inp_4897 v h) (by intro d hd; cases hd)))
def cl_28196 : CNF.NClause := [(38,false),(82,true),(71,false),(89,true),(64,false),(73,false),(80,false)]
theorem der_28196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28196 :=
  CNF.rup_sound cl_28196 [cl_4962,cl_28195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4962 v h) (hints_cons _ _ _ (der_28195 v h) (by intro d hd; cases hd)))
def cl_28197 : CNF.NClause := [(38,false),(82,true),(7,false),(73,false),(80,false),(71,false),(89,true)]
theorem der_28197 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28197 :=
  CNF.rup_sound cl_28197 [cl_4963,cl_28195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4963 v h) (hints_cons _ _ _ (der_28195 v h) (by intro d hd; cases hd)))
def cl_28198 : CNF.NClause := [(38,false),(82,true),(7,true),(71,false),(64,true),(73,false),(80,false)]
theorem der_28198 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28198 :=
  CNF.rup_sound cl_28198 [cl_4964,cl_28135] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4964 v h) (hints_cons _ _ _ (der_28135 v h) (by intro d hd; cases hd)))
def cl_28199 : CNF.NClause := [(38,false),(82,true),(7,false),(89,true),(64,false),(73,false),(80,false)]
theorem der_28199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28199 :=
  CNF.rup_sound cl_28199 [cl_4965,cl_28195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4965 v h) (hints_cons _ _ _ (der_28195 v h) (by intro d hd; cases hd)))
def cl_28200 : CNF.NClause := [(38,false),(82,true),(89,true),(64,false),(73,false),(71,true),(80,false)]
theorem der_28200 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28200 :=
  CNF.rup_sound cl_28200 [cl_4966,cl_28199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4966 v h) (hints_cons _ _ _ (der_28199 v h) (by intro d hd; cases hd)))
def cl_28201 : CNF.NClause := [(38,false),(73,false),(7,false),(71,true),(80,false),(82,true),(89,true)]
theorem der_28201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28201 :=
  CNF.rup_sound cl_28201 [cl_4967,cl_28199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4967 v h) (hints_cons _ _ _ (der_28199 v h) (by intro d hd; cases hd)))
def cl_28202 : CNF.NClause := [(38,false),(73,false),(7,true),(64,true),(71,true),(80,false),(89,true)]
theorem der_28202 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28202 :=
  CNF.rup_sound cl_28202 [cl_4968,cl_28170] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4968 v h) (hints_cons _ _ _ (der_28170 v h) (by intro d hd; cases hd)))
def cl_28203 : CNF.NClause := [(38,false),(82,true),(7,false),(64,false),(71,false),(80,false),(89,true)]
theorem der_28203 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28203 :=
  CNF.rup_sound cl_28203 [cl_4969,cl_28195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4969 v h) (hints_cons _ _ _ (der_28195 v h) (by intro d hd; cases hd)))
def cl_28204 : CNF.NClause := [(38,false),(7,true),(71,false),(64,false),(73,true),(80,false),(89,true)]
theorem der_28204 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28204 :=
  CNF.rup_sound cl_28204 [cl_4970,cl_28176] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4970 v h) (hints_cons _ _ _ (der_28176 v h) (by intro d hd; cases hd)))
def cl_28205 : CNF.NClause := [(38,false),(82,true),(7,false),(64,true),(71,false),(73,true),(80,false)]
theorem der_28205 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28205 :=
  CNF.rup_sound cl_28205 [cl_4971,cl_28142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4971 v h) (hints_cons _ _ _ (der_28142 v h) (by intro d hd; cases hd)))
def cl_28206 : CNF.NClause := [(38,false),(82,true),(64,true),(71,false),(73,true),(80,false),(89,true)]
theorem der_28206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28206 :=
  CNF.rup_sound cl_28206 [cl_4972,cl_28205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4972 v h) (hints_cons _ _ _ (der_28205 v h) (by intro d hd; cases hd)))
def cl_28207 : CNF.NClause := [(38,false),(82,true),(7,false),(64,false),(73,true),(80,false),(71,true)]
theorem der_28207 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28207 :=
  CNF.rup_sound cl_28207 [cl_4973,cl_28144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4973 v h) (hints_cons _ _ _ (der_28144 v h) (by intro d hd; cases hd)))
def cl_28208 : CNF.NClause := [(38,false),(82,true),(64,false),(73,true),(80,false),(71,true),(89,true)]
theorem der_28208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28208 :=
  CNF.rup_sound cl_28208 [cl_4974,cl_28207] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4974 v h) (hints_cons _ _ _ (der_28207 v h) (by intro d hd; cases hd)))
def cl_28209 : CNF.NClause := [(38,false),(73,true),(7,false),(64,true),(71,true),(80,false),(82,true)]
theorem der_28209 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28209 :=
  CNF.rup_sound cl_28209 [cl_4975,cl_28146] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4975 v h) (hints_cons _ _ _ (der_28146 v h) (by intro d hd; cases hd)))
def cl_28210 : CNF.NClause := [(38,false),(73,true),(7,true),(64,true),(71,true),(80,false),(89,true)]
theorem der_28210 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28210 :=
  CNF.rup_sound cl_28210 [cl_4976,cl_28178] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4976 v h) (hints_cons _ _ _ (der_28178 v h) (by intro d hd; cases hd)))
def cl_28211 : CNF.NClause := [(38,false),(7,false),(64,false),(71,false),(73,false),(82,true),(89,true)]
theorem der_28211 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28211 :=
  CNF.rup_sound cl_28211 [cl_4977,cl_28199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4977 v h) (hints_cons _ _ _ (der_28199 v h) (by intro d hd; cases hd)))
def cl_28212 : CNF.NClause := [(38,false),(7,true),(71,false),(64,false),(73,false),(80,true),(89,true)]
theorem der_28212 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28212 :=
  CNF.rup_sound cl_28212 [cl_4978,cl_28180] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4978 v h) (hints_cons _ _ _ (der_28180 v h) (by intro d hd; cases hd)))
def cl_28213 : CNF.NClause := [(38,false),(82,true),(7,false),(64,true),(73,false),(71,false),(89,true)]
theorem der_28213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28213 :=
  CNF.rup_sound cl_28213 [cl_4979,cl_28197] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4979 v h) (hints_cons _ _ _ (der_28197 v h) (by intro d hd; cases hd)))
def cl_28214 : CNF.NClause := [(38,false),(82,true),(7,true),(80,true),(71,false),(73,false),(64,true)]
theorem der_28214 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28214 :=
  CNF.rup_sound cl_28214 [cl_4980,cl_28151] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4980 v h) (hints_cons _ _ _ (der_28151 v h) (by intro d hd; cases hd)))
def cl_28215 : CNF.NClause := [(38,false),(7,false),(64,false),(71,true),(73,false),(82,true),(89,true)]
theorem der_28215 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28215 :=
  CNF.rup_sound cl_28215 [cl_4981,cl_28199] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4981 v h) (hints_cons _ _ _ (der_28199 v h) (by intro d hd; cases hd)))
def cl_28216 : CNF.NClause := [(38,false),(80,true),(64,false),(71,true),(73,false),(82,true),(89,true)]
theorem der_28216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28216 :=
  CNF.rup_sound cl_28216 [cl_4982,cl_28215] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4982 v h) (hints_cons _ _ _ (der_28215 v h) (by intro d hd; cases hd)))
def cl_28218 : CNF.NClause := [(38,false),(80,true),(7,true),(64,true),(71,true),(73,false),(89,true)]
theorem der_28218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28218 :=
  CNF.rup_sound cl_28218 [cl_4984,cl_28186] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4984 v h) (hints_cons _ _ _ (der_28186 v h) (by intro d hd; cases hd)))
def cl_28219 : CNF.NClause := [(38,false),(82,true),(7,false),(64,false),(71,false),(73,true),(80,true)]
theorem der_28219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28219 :=
  CNF.rup_sound cl_28219 [cl_4985,cl_28156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4985 v h) (hints_cons _ _ _ (der_28156 v h) (by intro d hd; cases hd)))
def cl_28220 : CNF.NClause := [(38,false),(82,true),(71,false),(64,false),(73,true),(80,true),(89,true)]
theorem der_28220 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28220 :=
  CNF.rup_sound cl_28220 [cl_4986,cl_28219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4986 v h) (hints_cons _ _ _ (der_28219 v h) (by intro d hd; cases hd)))
def cl_28221 : CNF.NClause := [(38,false),(82,true),(7,false),(64,true),(71,false),(73,true),(89,true)]
theorem der_28221 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28221 :=
  CNF.rup_sound cl_28221 [cl_4987,cl_28205] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4987 v h) (hints_cons _ _ _ (der_28205 v h) (by intro d hd; cases hd)))
def cl_28222 : CNF.NClause := [(38,false),(82,true),(7,true),(64,true),(71,false),(80,true),(89,true)]
theorem der_28222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28222 :=
  CNF.rup_sound cl_28222 [cl_4988,cl_28214] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4988 v h) (hints_cons _ _ _ (der_28214 v h) (by intro d hd; cases hd)))
def cl_28223 : CNF.NClause := [(38,false),(7,false),(64,false),(73,true),(71,true),(82,true),(89,true)]
theorem der_28223 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28223 :=
  CNF.rup_sound cl_28223 [cl_4989,cl_28207] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4989 v h) (hints_cons _ _ _ (der_28207 v h) (by intro d hd; cases hd)))
def cl_28224 : CNF.NClause := [(38,false),(80,true),(64,false),(73,true),(71,true),(82,true),(89,true)]
theorem der_28224 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28224 :=
  CNF.rup_sound cl_28224 [cl_4990,cl_28223] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4990 v h) (hints_cons _ _ _ (der_28223 v h) (by intro d hd; cases hd)))
def cl_28225 : CNF.NClause := [(38,false),(80,true),(7,false),(64,true),(71,true),(73,true),(82,true)]
theorem der_28225 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28225 :=
  CNF.rup_sound cl_28225 [cl_4991,cl_28162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4991 v h) (hints_cons _ _ _ (der_28162 v h) (by intro d hd; cases hd)))
def cl_28226 : CNF.NClause := [(38,false),(80,true),(7,true),(64,true),(71,true),(73,true),(89,true)]
theorem der_28226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28226 :=
  CNF.rup_sound cl_28226 [cl_4992,cl_28194] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4992 v h) (hints_cons _ _ _ (der_28194 v h) (by intro d hd; cases hd)))
def cl_28227 : CNF.NClause := [(59,false),(70,false),(28,true),(73,false),(84,false),(81,false),(90,false)]
theorem der_28227 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28227 :=
  CNF.rup_sound cl_28227 [cl_7554,cl_7556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7554 v h) (hints_cons _ _ _ (inp_7556 v h) (by intro d hd; cases hd)))
def cl_28228 : CNF.NClause := [(59,false),(62,true),(84,false),(81,false),(70,false),(90,false),(73,false)]
theorem der_28228 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28228 :=
  CNF.rup_sound cl_28228 [cl_7555,cl_28227] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7555 v h) (hints_cons _ _ _ (der_28227 v h) (by intro d hd; cases hd)))
def cl_28229 : CNF.NClause := [(59,false),(70,true),(62,false),(73,false),(84,false),(90,false),(81,false)]
theorem der_28229 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28229 :=
  CNF.rup_sound cl_28229 [cl_7558,cl_7557] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7558 v h) (hints_cons _ _ _ (inp_7557 v h) (by intro d hd; cases hd)))
def cl_28230 : CNF.NClause := [(59,false),(28,false),(62,true),(73,false),(81,false),(84,false),(90,false)]
theorem der_28230 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28230 :=
  CNF.rup_sound cl_28230 [cl_7559,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7559 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28231 : CNF.NClause := [(59,false),(28,true),(84,false),(73,false),(90,false),(81,false),(62,true)]
theorem der_28231 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28231 :=
  CNF.rup_sound cl_28231 [cl_7560,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7560 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28232 : CNF.NClause := [(59,false),(70,false),(62,false),(81,false),(73,true),(90,false),(84,false)]
theorem der_28232 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28232 :=
  CNF.rup_sound cl_28232 [cl_7562,cl_7561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7562 v h) (hints_cons _ _ _ (inp_7561 v h) (by intro d hd; cases hd)))
def cl_28233 : CNF.NClause := [(59,false),(62,true),(28,false),(81,false),(70,false),(84,false),(90,false)]
theorem der_28233 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28233 :=
  CNF.rup_sound cl_28233 [cl_7563,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7563 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28234 : CNF.NClause := [(59,false),(62,true),(28,true),(81,false),(84,false),(70,false),(90,false)]
theorem der_28234 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28234 :=
  CNF.rup_sound cl_28234 [cl_7564,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7564 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28235 : CNF.NClause := [(59,false),(70,true),(28,false),(81,false),(62,false),(84,false),(90,false)]
theorem der_28235 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28235 :=
  CNF.rup_sound cl_28235 [cl_7565,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7565 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28236 : CNF.NClause := [(59,false),(70,true),(28,true),(81,false),(62,false),(84,false),(90,false)]
theorem der_28236 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28236 :=
  CNF.rup_sound cl_28236 [cl_7566,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7566 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28237 : CNF.NClause := [(59,false),(70,true),(28,false),(62,true),(81,false),(84,false),(90,false)]
theorem der_28237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28237 :=
  CNF.rup_sound cl_28237 [cl_7567,cl_28230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7567 v h) (hints_cons _ _ _ (der_28230 v h) (by intro d hd; cases hd)))
def cl_28238 : CNF.NClause := [(59,false),(70,true),(62,true),(73,true),(81,false),(84,false),(90,false)]
theorem der_28238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28238 :=
  CNF.rup_sound cl_28238 [cl_7568,cl_28237] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7568 v h) (hints_cons _ _ _ (der_28237 v h) (by intro d hd; cases hd)))
def cl_28239 : CNF.NClause := [(59,false),(81,true),(70,false),(73,false),(62,false),(84,false),(90,false)]
theorem der_28239 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28239 :=
  CNF.rup_sound cl_28239 [cl_7570,cl_7569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7570 v h) (hints_cons _ _ _ (inp_7569 v h) (by intro d hd; cases hd)))
def cl_28240 : CNF.NClause := [(59,false),(28,false),(62,true),(73,false),(70,false),(84,false),(90,false)]
theorem der_28240 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28240 :=
  CNF.rup_sound cl_28240 [cl_7571,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7571 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28241 : CNF.NClause := [(59,false),(28,true),(62,true),(73,false),(70,false),(84,false),(90,false)]
theorem der_28241 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28241 :=
  CNF.rup_sound cl_28241 [cl_7572,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7572 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28242 : CNF.NClause := [(59,false),(28,false),(62,false),(73,false),(70,true),(84,false),(90,false)]
theorem der_28242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28242 :=
  CNF.rup_sound cl_28242 [cl_7573,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7573 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28243 : CNF.NClause := [(59,false),(28,true),(62,false),(73,false),(70,true),(84,false),(90,false)]
theorem der_28243 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28243 :=
  CNF.rup_sound cl_28243 [cl_7574,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7574 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28244 : CNF.NClause := [(59,false),(28,false),(70,true),(73,false),(62,true),(84,false),(90,false)]
theorem der_28244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28244 :=
  CNF.rup_sound cl_28244 [cl_7575,cl_28230] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7575 v h) (hints_cons _ _ _ (der_28230 v h) (by intro d hd; cases hd)))
def cl_28245 : CNF.NClause := [(59,false),(81,true),(70,true),(73,false),(62,true),(84,false),(90,false)]
theorem der_28245 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28245 :=
  CNF.rup_sound cl_28245 [cl_7576,cl_28244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7576 v h) (hints_cons _ _ _ (der_28244 v h) (by intro d hd; cases hd)))
def cl_28246 : CNF.NClause := [(59,false),(28,false),(70,false),(62,false),(73,true),(84,false),(90,false)]
theorem der_28246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28246 :=
  CNF.rup_sound cl_28246 [cl_7577,cl_28232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7577 v h) (hints_cons _ _ _ (der_28232 v h) (by intro d hd; cases hd)))
def cl_28247 : CNF.NClause := [(59,false),(28,true),(70,false),(62,false),(73,true),(84,false),(90,false)]
theorem der_28247 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28247 :=
  CNF.rup_sound cl_28247 [cl_7578,cl_28232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7578 v h) (hints_cons _ _ _ (der_28232 v h) (by intro d hd; cases hd)))
def cl_28248 : CNF.NClause := [(59,false),(28,false),(62,true),(70,false),(73,true),(84,false),(90,false)]
theorem der_28248 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28248 :=
  CNF.rup_sound cl_28248 [cl_7579,cl_28233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7579 v h) (hints_cons _ _ _ (der_28233 v h) (by intro d hd; cases hd)))
def cl_28249 : CNF.NClause := [(59,false),(81,true),(62,true),(70,false),(73,true),(84,false),(90,false)]
theorem der_28249 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28249 :=
  CNF.rup_sound cl_28249 [cl_7580,cl_28248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7580 v h) (hints_cons _ _ _ (der_28248 v h) (by intro d hd; cases hd)))
def cl_28250 : CNF.NClause := [(59,false),(28,false),(62,false),(73,true),(70,true),(84,false),(90,false)]
theorem der_28250 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28250 :=
  CNF.rup_sound cl_28250 [cl_7581,cl_28235] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7581 v h) (hints_cons _ _ _ (der_28235 v h) (by intro d hd; cases hd)))
def cl_28251 : CNF.NClause := [(59,false),(81,true),(62,false),(73,true),(70,true),(84,false),(90,false)]
theorem der_28251 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28251 :=
  CNF.rup_sound cl_28251 [cl_7582,cl_28250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7582 v h) (hints_cons _ _ _ (der_28250 v h) (by intro d hd; cases hd)))
def cl_28252 : CNF.NClause := [(59,false),(28,false),(70,true),(73,true),(62,true),(84,false),(90,false)]
theorem der_28252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28252 :=
  CNF.rup_sound cl_28252 [cl_7583,cl_28238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7583 v h) (hints_cons _ _ _ (der_28238 v h) (by intro d hd; cases hd)))
def cl_28253 : CNF.NClause := [(59,false),(28,true),(70,true),(73,true),(62,true),(84,false),(90,false)]
theorem der_28253 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28253 :=
  CNF.rup_sound cl_28253 [cl_7584,cl_28238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7584 v h) (hints_cons _ _ _ (der_28238 v h) (by intro d hd; cases hd)))
def cl_28254 : CNF.NClause := [(59,false),(84,true),(90,false),(73,false),(70,false),(62,false),(81,false)]
theorem der_28254 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28254 :=
  CNF.rup_sound cl_28254 [cl_7586,cl_7585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7586 v h) (hints_cons _ _ _ (inp_7585 v h) (by intro d hd; cases hd)))
def cl_28255 : CNF.NClause := [(59,false),(28,false),(62,true),(73,false),(81,false),(70,false),(90,false)]
theorem der_28255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28255 :=
  CNF.rup_sound cl_28255 [cl_7587,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7587 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28256 : CNF.NClause := [(59,false),(28,true),(62,true),(70,false),(73,false),(81,false),(90,false)]
theorem der_28256 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28256 :=
  CNF.rup_sound cl_28256 [cl_7588,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7588 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28257 : CNF.NClause := [(59,false),(28,false),(62,false),(73,false),(70,true),(81,false),(90,false)]
theorem der_28257 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28257 :=
  CNF.rup_sound cl_28257 [cl_7589,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7589 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28258 : CNF.NClause := [(59,false),(28,true),(62,false),(73,false),(81,false),(70,true),(90,false)]
theorem der_28258 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28258 :=
  CNF.rup_sound cl_28258 [cl_7590,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7590 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28259 : CNF.NClause := [(59,false),(28,false),(70,true),(73,false),(81,false),(62,true),(90,false)]
theorem der_28259 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28259 :=
  CNF.rup_sound cl_28259 [cl_7591,cl_28244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7591 v h) (hints_cons _ _ _ (der_28244 v h) (by intro d hd; cases hd)))
def cl_28260 : CNF.NClause := [(59,false),(84,true),(70,true),(73,false),(81,false),(62,true),(90,false)]
theorem der_28260 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28260 :=
  CNF.rup_sound cl_28260 [cl_7592,cl_28259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7592 v h) (hints_cons _ _ _ (der_28259 v h) (by intro d hd; cases hd)))
def cl_28261 : CNF.NClause := [(59,false),(28,false),(70,false),(62,false),(73,true),(81,false),(90,false)]
theorem der_28261 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28261 :=
  CNF.rup_sound cl_28261 [cl_7593,cl_28232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7593 v h) (hints_cons _ _ _ (der_28232 v h) (by intro d hd; cases hd)))
def cl_28262 : CNF.NClause := [(59,false),(28,true),(70,false),(62,false),(73,true),(81,false),(90,false)]
theorem der_28262 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28262 :=
  CNF.rup_sound cl_28262 [cl_7594,cl_28232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7594 v h) (hints_cons _ _ _ (der_28232 v h) (by intro d hd; cases hd)))
def cl_28263 : CNF.NClause := [(59,false),(84,true),(28,false),(70,false),(73,true),(81,false),(90,false)]
theorem der_28263 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28263 :=
  CNF.rup_sound cl_28263 [cl_7595,cl_28261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7595 v h) (hints_cons _ _ _ (der_28261 v h) (by intro d hd; cases hd)))
def cl_28264 : CNF.NClause := [(59,false),(84,true),(62,true),(70,false),(73,true),(81,false),(90,false)]
theorem der_28264 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28264 :=
  CNF.rup_sound cl_28264 [cl_7596,cl_28263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7596 v h) (hints_cons _ _ _ (der_28263 v h) (by intro d hd; cases hd)))
def cl_28265 : CNF.NClause := [(59,false),(28,false),(62,false),(73,true),(70,true),(81,false),(90,false)]
theorem der_28265 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28265 :=
  CNF.rup_sound cl_28265 [cl_7597,cl_28250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7597 v h) (hints_cons _ _ _ (der_28250 v h) (by intro d hd; cases hd)))
def cl_28266 : CNF.NClause := [(59,false),(84,true),(62,false),(73,true),(70,true),(81,false),(90,false)]
theorem der_28266 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28266 :=
  CNF.rup_sound cl_28266 [cl_7598,cl_28265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7598 v h) (hints_cons _ _ _ (der_28265 v h) (by intro d hd; cases hd)))
def cl_28267 : CNF.NClause := [(59,false),(28,false),(70,true),(73,true),(62,true),(81,false),(90,false)]
theorem der_28267 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28267 :=
  CNF.rup_sound cl_28267 [cl_7599,cl_28238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7599 v h) (hints_cons _ _ _ (der_28238 v h) (by intro d hd; cases hd)))
def cl_28268 : CNF.NClause := [(59,false),(28,true),(70,true),(73,true),(62,true),(81,false),(90,false)]
theorem der_28268 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28268 :=
  CNF.rup_sound cl_28268 [cl_7600,cl_28238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7600 v h) (hints_cons _ _ _ (der_28238 v h) (by intro d hd; cases hd)))
def cl_28269 : CNF.NClause := [(59,false),(28,false),(70,false),(73,false),(62,false),(81,true),(90,false)]
theorem der_28269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28269 :=
  CNF.rup_sound cl_28269 [cl_7601,cl_28239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7601 v h) (hints_cons _ _ _ (der_28239 v h) (by intro d hd; cases hd)))
def cl_28270 : CNF.NClause := [(59,false),(28,true),(70,false),(73,false),(62,false),(81,true),(90,false)]
theorem der_28270 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28270 :=
  CNF.rup_sound cl_28270 [cl_7602,cl_28239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7602 v h) (hints_cons _ _ _ (der_28239 v h) (by intro d hd; cases hd)))
def cl_28271 : CNF.NClause := [(59,false),(28,false),(62,true),(73,false),(70,false),(81,true),(90,false)]
theorem der_28271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28271 :=
  CNF.rup_sound cl_28271 [cl_7603,cl_28240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7603 v h) (hints_cons _ _ _ (der_28240 v h) (by intro d hd; cases hd)))
def cl_28272 : CNF.NClause := [(59,false),(28,true),(62,true),(73,false),(70,false),(81,true),(90,false)]
theorem der_28272 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28272 :=
  CNF.rup_sound cl_28272 [cl_7604,cl_28241] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7604 v h) (hints_cons _ _ _ (der_28241 v h) (by intro d hd; cases hd)))
def cl_28273 : CNF.NClause := [(59,false),(28,false),(62,false),(73,false),(70,true),(84,true),(90,false)]
theorem der_28273 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28273 :=
  CNF.rup_sound cl_28273 [cl_7605,cl_28257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7605 v h) (hints_cons _ _ _ (der_28257 v h) (by intro d hd; cases hd)))
def cl_28274 : CNF.NClause := [(59,false),(81,true),(62,false),(73,false),(70,true),(84,true),(90,false)]
theorem der_28274 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28274 :=
  CNF.rup_sound cl_28274 [cl_7606,cl_28273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7606 v h) (hints_cons _ _ _ (der_28273 v h) (by intro d hd; cases hd)))
def cl_28275 : CNF.NClause := [(59,false),(81,true),(28,false),(70,true),(73,false),(62,true),(90,false)]
theorem der_28275 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28275 :=
  CNF.rup_sound cl_28275 [cl_7607,cl_28244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7607 v h) (hints_cons _ _ _ (der_28244 v h) (by intro d hd; cases hd)))
def cl_28276 : CNF.NClause := [(59,false),(81,true),(28,true),(70,true),(73,false),(62,true),(90,false)]
theorem der_28276 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28276 :=
  CNF.rup_sound cl_28276 [cl_7608,cl_28245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7608 v h) (hints_cons _ _ _ (der_28245 v h) (by intro d hd; cases hd)))
def cl_28277 : CNF.NClause := [(59,false),(28,false),(70,false),(62,false),(73,true),(84,true),(90,false)]
theorem der_28277 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28277 :=
  CNF.rup_sound cl_28277 [cl_7609,cl_28261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7609 v h) (hints_cons _ _ _ (der_28261 v h) (by intro d hd; cases hd)))
def cl_28278 : CNF.NClause := [(59,false),(81,true),(28,true),(70,false),(62,false),(73,true),(90,false)]
theorem der_28278 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28278 :=
  CNF.rup_sound cl_28278 [cl_7610,cl_28247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7610 v h) (hints_cons _ _ _ (der_28247 v h) (by intro d hd; cases hd)))
def cl_28279 : CNF.NClause := [(59,false),(81,true),(28,false),(62,true),(70,false),(73,true),(90,false)]
theorem der_28279 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28279 :=
  CNF.rup_sound cl_28279 [cl_7611,cl_28248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7611 v h) (hints_cons _ _ _ (der_28248 v h) (by intro d hd; cases hd)))
def cl_28280 : CNF.NClause := [(59,false),(81,true),(28,true),(62,true),(70,false),(84,true),(90,false)]
theorem der_28280 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28280 :=
  CNF.rup_sound cl_28280 [cl_7612,cl_28272] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7612 v h) (hints_cons _ _ _ (der_28272 v h) (by intro d hd; cases hd)))
def cl_28281 : CNF.NClause := [(59,false),(81,true),(28,false),(62,false),(73,true),(70,true),(90,false)]
theorem der_28281 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28281 :=
  CNF.rup_sound cl_28281 [cl_7613,cl_28250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7613 v h) (hints_cons _ _ _ (der_28250 v h) (by intro d hd; cases hd)))
def cl_28282 : CNF.NClause := [(59,false),(81,true),(62,false),(73,true),(70,true),(84,true),(90,false)]
theorem der_28282 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28282 :=
  CNF.rup_sound cl_28282 [cl_7614,cl_28281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7614 v h) (hints_cons _ _ _ (der_28281 v h) (by intro d hd; cases hd)))
def cl_28283 : CNF.NClause := [(59,false),(81,true),(28,false),(70,true),(73,true),(84,true),(90,false)]
theorem der_28283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28283 :=
  CNF.rup_sound cl_28283 [cl_7615,cl_28281] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7615 v h) (hints_cons _ _ _ (der_28281 v h) (by intro d hd; cases hd)))
def cl_28284 : CNF.NClause := [(59,false),(81,true),(70,true),(73,true),(62,true),(84,true),(90,false)]
theorem der_28284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28284 :=
  CNF.rup_sound cl_28284 [cl_7616,cl_28283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7616 v h) (hints_cons _ _ _ (der_28283 v h) (by intro d hd; cases hd)))
def cl_28285 : CNF.NClause := [(59,false),(90,true),(28,true),(70,false),(81,false),(84,false),(73,false)]
theorem der_28285 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28285 :=
  CNF.rup_sound cl_28285 [cl_7618,cl_26332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7618 v h) (hints_cons _ _ _ (der_26332 v h) (by intro d hd; cases hd)))
def cl_28286 : CNF.NClause := [(59,false),(28,false),(84,false),(73,false),(81,false),(70,false),(62,true)]
theorem der_28286 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28286 :=
  CNF.rup_sound cl_28286 [cl_7619,cl_28228] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7619 v h) (hints_cons _ _ _ (der_28228 v h) (by intro d hd; cases hd)))
def cl_28287 : CNF.NClause := [(59,false),(28,false),(62,false),(73,false),(70,true),(84,false),(81,false)]
theorem der_28287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28287 :=
  CNF.rup_sound cl_28287 [cl_7621,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7621 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28288 : CNF.NClause := [(59,false),(28,true),(62,false),(73,false),(70,true),(84,false),(81,false)]
theorem der_28288 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28288 :=
  CNF.rup_sound cl_28288 [cl_7622,cl_28229] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7622 v h) (hints_cons _ _ _ (der_28229 v h) (by intro d hd; cases hd)))
def cl_28289 : CNF.NClause := [(59,false),(28,false),(70,true),(73,false),(81,false),(84,false),(62,true)]
theorem der_28289 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28289 :=
  CNF.rup_sound cl_28289 [cl_7623,cl_28244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7623 v h) (hints_cons _ _ _ (der_28244 v h) (by intro d hd; cases hd)))
def cl_28290 : CNF.NClause := [(59,false),(90,true),(28,true),(73,false),(81,false),(84,false),(62,true)]
theorem der_28290 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28290 :=
  CNF.rup_sound cl_28290 [cl_7624,cl_26332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7624 v h) (hints_cons _ _ _ (der_26332 v h) (by intro d hd; cases hd)))
def cl_28291 : CNF.NClause := [(59,false),(28,false),(70,false),(81,false),(73,true),(84,false),(62,false)]
theorem der_28291 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28291 :=
  CNF.rup_sound cl_28291 [cl_7625,cl_28232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7625 v h) (hints_cons _ _ _ (der_28232 v h) (by intro d hd; cases hd)))
def cl_28292 : CNF.NClause := [(59,false),(28,true),(70,false),(62,false),(73,true),(84,false),(81,false)]
theorem der_28292 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28292 :=
  CNF.rup_sound cl_28292 [cl_7626,cl_28232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7626 v h) (hints_cons _ _ _ (der_28232 v h) (by intro d hd; cases hd)))
def cl_28293 : CNF.NClause := [(59,false),(62,true),(28,false),(84,false),(70,false),(73,true),(81,false)]
theorem der_28293 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28293 :=
  CNF.rup_sound cl_28293 [cl_7627,cl_28233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7627 v h) (hints_cons _ _ _ (der_28233 v h) (by intro d hd; cases hd)))
def cl_28294 : CNF.NClause := [(59,false),(28,false),(62,false),(73,true),(70,true),(84,false),(81,false)]
theorem der_28294 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28294 :=
  CNF.rup_sound cl_28294 [cl_7629,cl_28250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7629 v h) (hints_cons _ _ _ (der_28250 v h) (by intro d hd; cases hd)))
def cl_28295 : CNF.NClause := [(59,false),(28,true),(62,false),(73,true),(70,true),(84,false),(81,false)]
theorem der_28295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28295 :=
  CNF.rup_sound cl_28295 [cl_7630,cl_28236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7630 v h) (hints_cons _ _ _ (der_28236 v h) (by intro d hd; cases hd)))
def cl_28296 : CNF.NClause := [(59,false),(28,false),(70,true),(73,true),(62,true),(84,false),(81,false)]
theorem der_28296 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28296 :=
  CNF.rup_sound cl_28296 [cl_7631,cl_28238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7631 v h) (hints_cons _ _ _ (der_28238 v h) (by intro d hd; cases hd)))
def cl_28297 : CNF.NClause := [(59,false),(28,true),(70,true),(73,true),(62,true),(84,false),(81,false)]
theorem der_28297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28297 :=
  CNF.rup_sound cl_28297 [cl_7632,cl_28238] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7632 v h) (hints_cons _ _ _ (der_28238 v h) (by intro d hd; cases hd)))
def cl_28298 : CNF.NClause := [(59,false),(81,true),(28,false),(70,false),(73,false),(62,false),(84,false)]
theorem der_28298 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28298 :=
  CNF.rup_sound cl_28298 [cl_7633,cl_28239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7633 v h) (hints_cons _ _ _ (der_28239 v h) (by intro d hd; cases hd)))
def cl_28299 : CNF.NClause := [(59,false),(81,true),(28,true),(70,false),(73,false),(62,false),(84,false)]
theorem der_28299 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28299 :=
  CNF.rup_sound cl_28299 [cl_7634,cl_28239] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7634 v h) (hints_cons _ _ _ (der_28239 v h) (by intro d hd; cases hd)))
def cl_28300 : CNF.NClause := [(59,false),(81,true),(28,false),(62,true),(73,false),(70,false),(84,false)]
theorem der_28300 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28300 :=
  CNF.rup_sound cl_28300 [cl_7635,cl_28240] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7635 v h) (hints_cons _ _ _ (der_28240 v h) (by intro d hd; cases hd)))
def cl_28301 : CNF.NClause := [(59,false),(28,false),(62,false),(73,false),(70,true),(84,false),(90,true)]
theorem der_28301 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28301 :=
  CNF.rup_sound cl_28301 [cl_7637,cl_28287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7637 v h) (hints_cons _ _ _ (der_28287 v h) (by intro d hd; cases hd)))
def cl_28302 : CNF.NClause := [(59,false),(81,true),(28,true),(62,false),(73,false),(70,true),(84,false)]
theorem der_28302 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28302 :=
  CNF.rup_sound cl_28302 [cl_7638,cl_28243] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7638 v h) (hints_cons _ _ _ (der_28243 v h) (by intro d hd; cases hd)))
def cl_28303 : CNF.NClause := [(59,false),(81,true),(28,false),(70,true),(73,false),(62,true),(84,false)]
theorem der_28303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28303 :=
  CNF.rup_sound cl_28303 [cl_7639,cl_28244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7639 v h) (hints_cons _ _ _ (der_28244 v h) (by intro d hd; cases hd)))
def cl_28304 : CNF.NClause := [(59,false),(81,true),(28,true),(70,true),(73,false),(62,true),(84,false)]
theorem der_28304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28304 :=
  CNF.rup_sound cl_28304 [cl_7640,cl_28245] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7640 v h) (hints_cons _ _ _ (der_28245 v h) (by intro d hd; cases hd)))
def cl_28305 : CNF.NClause := [(59,false),(81,true),(28,false),(70,false),(62,false),(73,true),(84,false)]
theorem der_28305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28305 :=
  CNF.rup_sound cl_28305 [cl_7641,cl_28246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7641 v h) (hints_cons _ _ _ (der_28246 v h) (by intro d hd; cases hd)))
def cl_28306 : CNF.NClause := [(59,false),(81,true),(28,true),(70,false),(62,false),(73,true),(84,false)]
theorem der_28306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28306 :=
  CNF.rup_sound cl_28306 [cl_7642,cl_28247] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7642 v h) (hints_cons _ _ _ (der_28247 v h) (by intro d hd; cases hd)))
def cl_28307 : CNF.NClause := [(59,false),(81,true),(28,false),(62,true),(70,false),(73,true),(84,false)]
theorem der_28307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28307 :=
  CNF.rup_sound cl_28307 [cl_7643,cl_28248] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7643 v h) (hints_cons _ _ _ (der_28248 v h) (by intro d hd; cases hd)))
def cl_28308 : CNF.NClause := [(59,false),(81,true),(28,false),(62,false),(73,true),(70,true),(84,false)]
theorem der_28308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28308 :=
  CNF.rup_sound cl_28308 [cl_7645,cl_28250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7645 v h) (hints_cons _ _ _ (der_28250 v h) (by intro d hd; cases hd)))
def cl_28309 : CNF.NClause := [(59,false),(81,true),(28,true),(62,false),(70,true),(84,false),(90,true)]
theorem der_28309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28309 :=
  CNF.rup_sound cl_28309 [cl_7646,cl_28302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7646 v h) (hints_cons _ _ _ (der_28302 v h) (by intro d hd; cases hd)))
def cl_28310 : CNF.NClause := [(59,false),(81,true),(28,false),(70,true),(73,true),(62,true),(84,false)]
theorem der_28310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28310 :=
  CNF.rup_sound cl_28310 [cl_7647,cl_28252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7647 v h) (hints_cons _ _ _ (der_28252 v h) (by intro d hd; cases hd)))
def cl_28311 : CNF.NClause := [(59,false),(28,true),(70,true),(73,true),(62,true),(84,false),(90,true)]
theorem der_28311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28311 :=
  CNF.rup_sound cl_28311 [cl_7648,cl_28297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7648 v h) (hints_cons _ _ _ (der_28297 v h) (by intro d hd; cases hd)))
def cl_28312 : CNF.NClause := [(59,false),(84,true),(28,false),(70,false),(73,false),(81,false),(62,false)]
theorem der_28312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28312 :=
  CNF.rup_sound cl_28312 [cl_7649,cl_7585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7649 v h) (hints_cons _ _ _ (inp_7585 v h) (by intro d hd; cases hd)))
def cl_28313 : CNF.NClause := [(59,false),(84,true),(70,false),(73,false),(81,false),(62,false),(90,true)]
theorem der_28313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28313 :=
  CNF.rup_sound cl_28313 [cl_7650,cl_28312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7650 v h) (hints_cons _ _ _ (der_28312 v h) (by intro d hd; cases hd)))
def cl_28314 : CNF.NClause := [(59,false),(28,false),(62,true),(73,false),(81,false),(84,true),(70,false)]
theorem der_28314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28314 :=
  CNF.rup_sound cl_28314 [cl_7651,cl_28255] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7651 v h) (hints_cons _ _ _ (der_28255 v h) (by intro d hd; cases hd)))
def cl_28315 : CNF.NClause := [(59,false),(84,true),(28,false),(62,false),(73,false),(70,true),(81,false)]
theorem der_28315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28315 :=
  CNF.rup_sound cl_28315 [cl_7653,cl_28257] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7653 v h) (hints_cons _ _ _ (der_28257 v h) (by intro d hd; cases hd)))
def cl_28316 : CNF.NClause := [(59,false),(84,true),(28,true),(62,false),(73,false),(81,false),(70,true)]
theorem der_28316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28316 :=
  CNF.rup_sound cl_28316 [cl_7654,cl_28258] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7654 v h) (hints_cons _ _ _ (der_28258 v h) (by intro d hd; cases hd)))
def cl_28317 : CNF.NClause := [(59,false),(84,true),(28,false),(70,true),(73,false),(81,false),(62,true)]
theorem der_28317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28317 :=
  CNF.rup_sound cl_28317 [cl_7655,cl_28259] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7655 v h) (hints_cons _ _ _ (der_28259 v h) (by intro d hd; cases hd)))
def cl_28318 : CNF.NClause := [(59,false),(84,true),(28,true),(70,true),(73,false),(81,false),(90,true)]
theorem der_28318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28318 :=
  CNF.rup_sound cl_28318 [cl_7656,cl_28316] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7656 v h) (hints_cons _ _ _ (der_28316 v h) (by intro d hd; cases hd)))
def cl_28319 : CNF.NClause := [(59,false),(84,true),(28,false),(70,false),(62,false),(73,true),(81,false)]
theorem der_28319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28319 :=
  CNF.rup_sound cl_28319 [cl_7657,cl_28261] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7657 v h) (hints_cons _ _ _ (der_28261 v h) (by intro d hd; cases hd)))
def cl_28320 : CNF.NClause := [(59,false),(84,true),(28,true),(70,false),(62,false),(73,true),(81,false)]
theorem der_28320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28320 :=
  CNF.rup_sound cl_28320 [cl_7658,cl_28262] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7658 v h) (hints_cons _ _ _ (der_28262 v h) (by intro d hd; cases hd)))
def cl_28321 : CNF.NClause := [(59,false),(84,true),(28,false),(62,true),(70,false),(73,true),(81,false)]
theorem der_28321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28321 :=
  CNF.rup_sound cl_28321 [cl_7659,cl_28263] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7659 v h) (hints_cons _ _ _ (der_28263 v h) (by intro d hd; cases hd)))
def cl_28322 : CNF.NClause := [(59,false),(84,true),(28,false),(62,false),(73,true),(70,true),(81,false)]
theorem der_28322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28322 :=
  CNF.rup_sound cl_28322 [cl_7661,cl_28265] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7661 v h) (hints_cons _ _ _ (der_28265 v h) (by intro d hd; cases hd)))
def cl_28323 : CNF.NClause := [(59,false),(84,true),(62,false),(73,true),(70,true),(81,false),(90,true)]
theorem der_28323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28323 :=
  CNF.rup_sound cl_28323 [cl_7662,cl_28322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7662 v h) (hints_cons _ _ _ (der_28322 v h) (by intro d hd; cases hd)))
def cl_28324 : CNF.NClause := [(59,false),(84,true),(28,false),(73,true),(62,true),(81,false),(90,true)]
theorem der_28324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28324 :=
  CNF.rup_sound cl_28324 [cl_7663,cl_28321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7663 v h) (hints_cons _ _ _ (der_28321 v h) (by intro d hd; cases hd)))
def cl_28325 : CNF.NClause := [(59,false),(28,true),(70,true),(73,true),(62,true),(81,false),(90,true)]
theorem der_28325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28325 :=
  CNF.rup_sound cl_28325 [cl_7664,cl_28297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7664 v h) (hints_cons _ _ _ (der_28297 v h) (by intro d hd; cases hd)))
def cl_28326 : CNF.NClause := [(59,false),(84,true),(28,false),(70,false),(73,false),(62,false),(90,true)]
theorem der_28326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28326 :=
  CNF.rup_sound cl_28326 [cl_7665,cl_28312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7665 v h) (hints_cons _ _ _ (der_28312 v h) (by intro d hd; cases hd)))
def cl_28327 : CNF.NClause := [(59,false),(84,true),(28,true),(70,false),(73,false),(62,false),(81,true)]
theorem der_28327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28327 :=
  CNF.rup_sound cl_28327 [cl_7666,cl_28270] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7666 v h) (hints_cons _ _ _ (der_28270 v h) (by intro d hd; cases hd)))
def cl_28328 : CNF.NClause := [(59,false),(28,false),(62,true),(73,false),(70,false),(81,true),(90,true)]
theorem der_28328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28328 :=
  CNF.rup_sound cl_28328 [cl_7667,cl_28300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7667 v h) (hints_cons _ _ _ (der_28300 v h) (by intro d hd; cases hd)))
def cl_28329 : CNF.NClause := [(59,false),(81,true),(28,false),(62,false),(73,false),(70,true),(84,true)]
theorem der_28329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28329 :=
  CNF.rup_sound cl_28329 [cl_7669,cl_28273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7669 v h) (hints_cons _ _ _ (der_28273 v h) (by intro d hd; cases hd)))
def cl_28330 : CNF.NClause := [(59,false),(81,true),(28,true),(62,false),(73,false),(70,true),(90,true)]
theorem der_28330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28330 :=
  CNF.rup_sound cl_28330 [cl_7670,cl_28302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7670 v h) (hints_cons _ _ _ (der_28302 v h) (by intro d hd; cases hd)))
def cl_28331 : CNF.NClause := [(59,false),(81,true),(28,false),(70,true),(73,false),(62,true),(84,true)]
theorem der_28331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28331 :=
  CNF.rup_sound cl_28331 [cl_7671,cl_28275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7671 v h) (hints_cons _ _ _ (der_28275 v h) (by intro d hd; cases hd)))
def cl_28332 : CNF.NClause := [(59,false),(81,true),(70,true),(73,false),(62,true),(84,true),(90,true)]
theorem der_28332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28332 :=
  CNF.rup_sound cl_28332 [cl_7672,cl_28331] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7672 v h) (hints_cons _ _ _ (der_28331 v h) (by intro d hd; cases hd)))
def cl_28333 : CNF.NClause := [(59,false),(81,true),(28,false),(70,false),(62,false),(73,true),(90,true)]
theorem der_28333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28333 :=
  CNF.rup_sound cl_28333 [cl_7673,cl_28305] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7673 v h) (hints_cons _ _ _ (der_28305 v h) (by intro d hd; cases hd)))
def cl_28334 : CNF.NClause := [(59,false),(28,true),(70,false),(62,false),(73,true),(84,true),(90,true)]
theorem der_28334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_28334 :=
  CNF.rup_sound cl_28334 [cl_7674,cl_28320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7674 v h) (hints_cons _ _ _ (der_28320 v h) (by intro d hd; cases hd)))
def chunk011 : List CNF.NClause := [cl_27816,cl_27817,cl_27818,cl_27819,cl_27820,cl_27821,cl_27822,cl_27824,cl_27825,cl_27826,cl_27827,cl_27828,cl_27829,cl_27830,cl_27831,cl_27832,cl_27833,cl_27834,cl_27835,cl_27836,cl_27837,cl_27838,cl_27839,cl_27840,cl_27841,cl_27842,cl_27843,cl_27844,cl_27845,cl_27846,cl_27847,cl_27849,cl_27850,cl_27851,cl_27853,cl_27855,cl_27856,cl_27857,cl_27858,cl_27859,cl_27860,cl_27863,cl_27864,cl_27865,cl_27867,cl_27868,cl_27869,cl_27870,cl_27871,cl_27872,cl_27873,cl_27874,cl_27875,cl_27876,cl_27877,cl_27878,cl_27879,cl_27880,cl_27881,cl_27882,cl_27883,cl_27884,cl_27885,cl_27886,cl_27887,cl_27888,cl_27889,cl_27890,cl_27891,cl_27892,cl_27893,cl_27894,cl_27895,cl_27896,cl_27897,cl_27898,cl_27899,cl_27900,cl_27901,cl_27902,cl_27903,cl_27904,cl_27905,cl_27906,cl_27907,cl_27908,cl_27909,cl_27910,cl_27911,cl_27912,cl_27913,cl_27914,cl_27915,cl_27916,cl_27917,cl_27918,cl_27919,cl_27920,cl_27921,cl_27922,cl_27923,cl_27924,cl_27925,cl_27926,cl_27927,cl_27928,cl_27929,cl_27930,cl_27931,cl_27932,cl_27933,cl_27934,cl_27935,cl_27936,cl_27937,cl_27938,cl_27939,cl_27940,cl_27941,cl_27942,cl_27943,cl_27944,cl_27945,cl_27946,cl_27947,cl_27948,cl_27949,cl_27950,cl_27951,cl_27952,cl_27953,cl_27954,cl_27955,cl_27956,cl_27957,cl_27958,cl_27959,cl_27960,cl_27961,cl_27962,cl_27963,cl_27964,cl_27965,cl_27967,cl_27968,cl_27969,cl_27970,cl_27971,cl_27972,cl_27973,cl_27974,cl_27975,cl_27976,cl_27977,cl_27978,cl_27979,cl_27981,cl_27983,cl_27984,cl_27985,cl_27987,cl_27988,cl_27989,cl_27990,cl_27991,cl_27992,cl_27993,cl_27994,cl_27995,cl_27996,cl_27997,cl_27998,cl_27999,cl_28000,cl_28001,cl_28002,cl_28003,cl_28004,cl_28005,cl_28006,cl_28007,cl_28008,cl_28009,cl_28010,cl_28011,cl_28013,cl_28014,cl_28015,cl_28016,cl_28017,cl_28018,cl_28019,cl_28020,cl_28021,cl_28022,cl_28023,cl_28024,cl_28025,cl_28026,cl_28027,cl_28028,cl_28029,cl_28030,cl_28031,cl_28032,cl_28033,cl_28034,cl_28035,cl_28036,cl_28037,cl_28038,cl_28039,cl_28040,cl_28041,cl_28042,cl_28043,cl_28044,cl_28045,cl_28046,cl_28047,cl_28048,cl_28049,cl_28050,cl_28051,cl_28052,cl_28053,cl_28054,cl_28055,cl_28056,cl_28058,cl_28059,cl_28060,cl_28061,cl_28062,cl_28063,cl_28064,cl_28065,cl_28066,cl_28067,cl_28068,cl_28069,cl_28070,cl_28072,cl_28074,cl_28075,cl_28076,cl_28077,cl_28078,cl_28079,cl_28080,cl_28081,cl_28082,cl_28083,cl_28084,cl_28085,cl_28086,cl_28087,cl_28088,cl_28089,cl_28090,cl_28091,cl_28092,cl_28093,cl_28094,cl_28095,cl_28096,cl_28097,cl_28098,cl_28100,cl_28102,cl_28104,cl_28105,cl_28106,cl_28107,cl_28108,cl_28109,cl_28110,cl_28111,cl_28112,cl_28113,cl_28114,cl_28115,cl_28116,cl_28117,cl_28118,cl_28119,cl_28120,cl_28121,cl_28122,cl_28123,cl_28124,cl_28125,cl_28126,cl_28127,cl_28128,cl_28129,cl_28130,cl_28131,cl_28132,cl_28133,cl_28134,cl_28135,cl_28136,cl_28137,cl_28138,cl_28139,cl_28140,cl_28141,cl_28142,cl_28143,cl_28144,cl_28145,cl_28146,cl_28147,cl_28148,cl_28149,cl_28150,cl_28151,cl_28152,cl_28153,cl_28154,cl_28155,cl_28156,cl_28157,cl_28158,cl_28159,cl_28160,cl_28161,cl_28162,cl_28163,cl_28164,cl_28165,cl_28166,cl_28167,cl_28168,cl_28169,cl_28170,cl_28171,cl_28172,cl_28173,cl_28174,cl_28175,cl_28176,cl_28177,cl_28178,cl_28179,cl_28180,cl_28181,cl_28182,cl_28183,cl_28184,cl_28185,cl_28186,cl_28187,cl_28188,cl_28189,cl_28190,cl_28191,cl_28192,cl_28193,cl_28194,cl_28195,cl_28196,cl_28197,cl_28198,cl_28199,cl_28200,cl_28201,cl_28202,cl_28203,cl_28204,cl_28205,cl_28206,cl_28207,cl_28208,cl_28209,cl_28210,cl_28211,cl_28212,cl_28213,cl_28214,cl_28215,cl_28216,cl_28218,cl_28219,cl_28220,cl_28221,cl_28222,cl_28223,cl_28224,cl_28225,cl_28226,cl_28227,cl_28228,cl_28229,cl_28230,cl_28231,cl_28232,cl_28233,cl_28234,cl_28235,cl_28236,cl_28237,cl_28238,cl_28239,cl_28240,cl_28241,cl_28242,cl_28243,cl_28244,cl_28245,cl_28246,cl_28247,cl_28248,cl_28249,cl_28250,cl_28251,cl_28252,cl_28253,cl_28254,cl_28255,cl_28256,cl_28257,cl_28258,cl_28259,cl_28260,cl_28261,cl_28262,cl_28263,cl_28264,cl_28265,cl_28266,cl_28267,cl_28268,cl_28269,cl_28270,cl_28271,cl_28272,cl_28273,cl_28274,cl_28275,cl_28276,cl_28277,cl_28278,cl_28279,cl_28280,cl_28281,cl_28282,cl_28283,cl_28284,cl_28285,cl_28286,cl_28287,cl_28288,cl_28289,cl_28290,cl_28291,cl_28292,cl_28293,cl_28294,cl_28295,cl_28296,cl_28297,cl_28298,cl_28299,cl_28300,cl_28301,cl_28302,cl_28303,cl_28304,cl_28305,cl_28306,cl_28307,cl_28308,cl_28309,cl_28310,cl_28311,cl_28312,cl_28313,cl_28314,cl_28315,cl_28316,cl_28317,cl_28318,cl_28319,cl_28320,cl_28321,cl_28322,cl_28323,cl_28324,cl_28325,cl_28326,cl_28327,cl_28328,cl_28329,cl_28330,cl_28331,cl_28332,cl_28333,cl_28334]
theorem chunk_sound011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk011, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_27816 v h) (hints_cons _ _ _ (der_27817 v h) (hints_cons _ _ _ (der_27818 v h) (hints_cons _ _ _ (der_27819 v h) (hints_cons _ _ _ (der_27820 v h) (hints_cons _ _ _ (der_27821 v h) (hints_cons _ _ _ (der_27822 v h) (hints_cons _ _ _ (der_27824 v h) (hints_cons _ _ _ (der_27825 v h) (hints_cons _ _ _ (der_27826 v h) (hints_cons _ _ _ (der_27827 v h) (hints_cons _ _ _ (der_27828 v h) (hints_cons _ _ _ (der_27829 v h) (hints_cons _ _ _ (der_27830 v h) (hints_cons _ _ _ (der_27831 v h) (hints_cons _ _ _ (der_27832 v h) (hints_cons _ _ _ (der_27833 v h) (hints_cons _ _ _ (der_27834 v h) (hints_cons _ _ _ (der_27835 v h) (hints_cons _ _ _ (der_27836 v h) (hints_cons _ _ _ (der_27837 v h) (hints_cons _ _ _ (der_27838 v h) (hints_cons _ _ _ (der_27839 v h) (hints_cons _ _ _ (der_27840 v h) (hints_cons _ _ _ (der_27841 v h) (hints_cons _ _ _ (der_27842 v h) (hints_cons _ _ _ (der_27843 v h) (hints_cons _ _ _ (der_27844 v h) (hints_cons _ _ _ (der_27845 v h) (hints_cons _ _ _ (der_27846 v h) (hints_cons _ _ _ (der_27847 v h) (hints_cons _ _ _ (der_27849 v h) (hints_cons _ _ _ (der_27850 v h) (hints_cons _ _ _ (der_27851 v h) (hints_cons _ _ _ (der_27853 v h) (hints_cons _ _ _ (der_27855 v h) (hints_cons _ _ _ (der_27856 v h) (hints_cons _ _ _ (der_27857 v h) (hints_cons _ _ _ (der_27858 v h) (hints_cons _ _ _ (der_27859 v h) (hints_cons _ _ _ (der_27860 v h) (hints_cons _ _ _ (der_27863 v h) (hints_cons _ _ _ (der_27864 v h) (hints_cons _ _ _ (der_27865 v h) (hints_cons _ _ _ (der_27867 v h) (hints_cons _ _ _ (der_27868 v h) (hints_cons _ _ _ (der_27869 v h) (hints_cons _ _ _ (der_27870 v h) (hints_cons _ _ _ (der_27871 v h) (hints_cons _ _ _ (der_27872 v h) (hints_cons _ _ _ (der_27873 v h) (hints_cons _ _ _ (der_27874 v h) (hints_cons _ _ _ (der_27875 v h) (hints_cons _ _ _ (der_27876 v h) (hints_cons _ _ _ (der_27877 v h) (hints_cons _ _ _ (der_27878 v h) (hints_cons _ _ _ (der_27879 v h) (hints_cons _ _ _ (der_27880 v h) (hints_cons _ _ _ (der_27881 v h) (hints_cons _ _ _ (der_27882 v h) (hints_cons _ _ _ (der_27883 v h) (hints_cons _ _ _ (der_27884 v h) (hints_cons _ _ _ (der_27885 v h) (hints_cons _ _ _ (der_27886 v h) (hints_cons _ _ _ (der_27887 v h) (hints_cons _ _ _ (der_27888 v h) (hints_cons _ _ _ (der_27889 v h) (hints_cons _ _ _ (der_27890 v h) (hints_cons _ _ _ (der_27891 v h) (hints_cons _ _ _ (der_27892 v h) (hints_cons _ _ _ (der_27893 v h) (hints_cons _ _ _ (der_27894 v h) (hints_cons _ _ _ (der_27895 v h) (hints_cons _ _ _ (der_27896 v h) (hints_cons _ _ _ (der_27897 v h) (hints_cons _ _ _ (der_27898 v h) (hints_cons _ _ _ (der_27899 v h) (hints_cons _ _ _ (der_27900 v h) (hints_cons _ _ _ (der_27901 v h) (hints_cons _ _ _ (der_27902 v h) (hints_cons _ _ _ (der_27903 v h) (hints_cons _ _ _ (der_27904 v h) (hints_cons _ _ _ (der_27905 v h) (hints_cons _ _ _ (der_27906 v h) (hints_cons _ _ _ (der_27907 v h) (hints_cons _ _ _ (der_27908 v h) (hints_cons _ _ _ (der_27909 v h) (hints_cons _ _ _ (der_27910 v h) (hints_cons _ _ _ (der_27911 v h) (hints_cons _ _ _ (der_27912 v h) (hints_cons _ _ _ (der_27913 v h) (hints_cons _ _ _ (der_27914 v h) (hints_cons _ _ _ (der_27915 v h) (hints_cons _ _ _ (der_27916 v h) (hints_cons _ _ _ (der_27917 v h) (hints_cons _ _ _ (der_27918 v h) (hints_cons _ _ _ (der_27919 v h) (hints_cons _ _ _ (der_27920 v h) (hints_cons _ _ _ (der_27921 v h) (hints_cons _ _ _ (der_27922 v h) (hints_cons _ _ _ (der_27923 v h) (hints_cons _ _ _ (der_27924 v h) (hints_cons _ _ _ (der_27925 v h) (hints_cons _ _ _ (der_27926 v h) (hints_cons _ _ _ (der_27927 v h) (hints_cons _ _ _ (der_27928 v h) (hints_cons _ _ _ (der_27929 v h) (hints_cons _ _ _ (der_27930 v h) (hints_cons _ _ _ (der_27931 v h) (hints_cons _ _ _ (der_27932 v h) (hints_cons _ _ _ (der_27933 v h) (hints_cons _ _ _ (der_27934 v h) (hints_cons _ _ _ (der_27935 v h) (hints_cons _ _ _ (der_27936 v h) (hints_cons _ _ _ (der_27937 v h) (hints_cons _ _ _ (der_27938 v h) (hints_cons _ _ _ (der_27939 v h) (hints_cons _ _ _ (der_27940 v h) (hints_cons _ _ _ (der_27941 v h) (hints_cons _ _ _ (der_27942 v h) (hints_cons _ _ _ (der_27943 v h) (hints_cons _ _ _ (der_27944 v h) (hints_cons _ _ _ (der_27945 v h) (hints_cons _ _ _ (der_27946 v h) (hints_cons _ _ _ (der_27947 v h) (hints_cons _ _ _ (der_27948 v h) (hints_cons _ _ _ (der_27949 v h) (hints_cons _ _ _ (der_27950 v h) (hints_cons _ _ _ (der_27951 v h) (hints_cons _ _ _ (der_27952 v h) (hints_cons _ _ _ (der_27953 v h) (hints_cons _ _ _ (der_27954 v h) (hints_cons _ _ _ (der_27955 v h) (hints_cons _ _ _ (der_27956 v h) (hints_cons _ _ _ (der_27957 v h) (hints_cons _ _ _ (der_27958 v h) (hints_cons _ _ _ (der_27959 v h) (hints_cons _ _ _ (der_27960 v h) (hints_cons _ _ _ (der_27961 v h) (hints_cons _ _ _ (der_27962 v h) (hints_cons _ _ _ (der_27963 v h) (hints_cons _ _ _ (der_27964 v h) (hints_cons _ _ _ (der_27965 v h) (hints_cons _ _ _ (der_27967 v h) (hints_cons _ _ _ (der_27968 v h) (hints_cons _ _ _ (der_27969 v h) (hints_cons _ _ _ (der_27970 v h) (hints_cons _ _ _ (der_27971 v h) (hints_cons _ _ _ (der_27972 v h) (hints_cons _ _ _ (der_27973 v h) (hints_cons _ _ _ (der_27974 v h) (hints_cons _ _ _ (der_27975 v h) (hints_cons _ _ _ (der_27976 v h) (hints_cons _ _ _ (der_27977 v h) (hints_cons _ _ _ (der_27978 v h) (hints_cons _ _ _ (der_27979 v h) (hints_cons _ _ _ (der_27981 v h) (hints_cons _ _ _ (der_27983 v h) (hints_cons _ _ _ (der_27984 v h) (hints_cons _ _ _ (der_27985 v h) (hints_cons _ _ _ (der_27987 v h) (hints_cons _ _ _ (der_27988 v h) (hints_cons _ _ _ (der_27989 v h) (hints_cons _ _ _ (der_27990 v h) (hints_cons _ _ _ (der_27991 v h) (hints_cons _ _ _ (der_27992 v h) (hints_cons _ _ _ (der_27993 v h) (hints_cons _ _ _ (der_27994 v h) (hints_cons _ _ _ (der_27995 v h) (hints_cons _ _ _ (der_27996 v h) (hints_cons _ _ _ (der_27997 v h) (hints_cons _ _ _ (der_27998 v h) (hints_cons _ _ _ (der_27999 v h) (hints_cons _ _ _ (der_28000 v h) (hints_cons _ _ _ (der_28001 v h) (hints_cons _ _ _ (der_28002 v h) (hints_cons _ _ _ (der_28003 v h) (hints_cons _ _ _ (der_28004 v h) (hints_cons _ _ _ (der_28005 v h) (hints_cons _ _ _ (der_28006 v h) (hints_cons _ _ _ (der_28007 v h) (hints_cons _ _ _ (der_28008 v h) (hints_cons _ _ _ (der_28009 v h) (hints_cons _ _ _ (der_28010 v h) (hints_cons _ _ _ (der_28011 v h) (hints_cons _ _ _ (der_28013 v h) (hints_cons _ _ _ (der_28014 v h) (hints_cons _ _ _ (der_28015 v h) (hints_cons _ _ _ (der_28016 v h) (hints_cons _ _ _ (der_28017 v h) (hints_cons _ _ _ (der_28018 v h) (hints_cons _ _ _ (der_28019 v h) (hints_cons _ _ _ (der_28020 v h) (hints_cons _ _ _ (der_28021 v h) (hints_cons _ _ _ (der_28022 v h) (hints_cons _ _ _ (der_28023 v h) (hints_cons _ _ _ (der_28024 v h) (hints_cons _ _ _ (der_28025 v h) (hints_cons _ _ _ (der_28026 v h) (hints_cons _ _ _ (der_28027 v h) (hints_cons _ _ _ (der_28028 v h) (hints_cons _ _ _ (der_28029 v h) (hints_cons _ _ _ (der_28030 v h) (hints_cons _ _ _ (der_28031 v h) (hints_cons _ _ _ (der_28032 v h) (hints_cons _ _ _ (der_28033 v h) (hints_cons _ _ _ (der_28034 v h) (hints_cons _ _ _ (der_28035 v h) (hints_cons _ _ _ (der_28036 v h) (hints_cons _ _ _ (der_28037 v h) (hints_cons _ _ _ (der_28038 v h) (hints_cons _ _ _ (der_28039 v h) (hints_cons _ _ _ (der_28040 v h) (hints_cons _ _ _ (der_28041 v h) (hints_cons _ _ _ (der_28042 v h) (hints_cons _ _ _ (der_28043 v h) (hints_cons _ _ _ (der_28044 v h) (hints_cons _ _ _ (der_28045 v h) (hints_cons _ _ _ (der_28046 v h) (hints_cons _ _ _ (der_28047 v h) (hints_cons _ _ _ (der_28048 v h) (hints_cons _ _ _ (der_28049 v h) (hints_cons _ _ _ (der_28050 v h) (hints_cons _ _ _ (der_28051 v h) (hints_cons _ _ _ (der_28052 v h) (hints_cons _ _ _ (der_28053 v h) (hints_cons _ _ _ (der_28054 v h) (hints_cons _ _ _ (der_28055 v h) (hints_cons _ _ _ (der_28056 v h) (hints_cons _ _ _ (der_28058 v h) (hints_cons _ _ _ (der_28059 v h) (hints_cons _ _ _ (der_28060 v h) (hints_cons _ _ _ (der_28061 v h) (hints_cons _ _ _ (der_28062 v h) (hints_cons _ _ _ (der_28063 v h) (hints_cons _ _ _ (der_28064 v h) (hints_cons _ _ _ (der_28065 v h) (hints_cons _ _ _ (der_28066 v h) (hints_cons _ _ _ (der_28067 v h) (hints_cons _ _ _ (der_28068 v h) (hints_cons _ _ _ (der_28069 v h) (hints_cons _ _ _ (der_28070 v h) (hints_cons _ _ _ (der_28072 v h) (hints_cons _ _ _ (der_28074 v h) (hints_cons _ _ _ (der_28075 v h) (hints_cons _ _ _ (der_28076 v h) (hints_cons _ _ _ (der_28077 v h) (hints_cons _ _ _ (der_28078 v h) (hints_cons _ _ _ (der_28079 v h) (hints_cons _ _ _ (der_28080 v h) (hints_cons _ _ _ (der_28081 v h) (hints_cons _ _ _ (der_28082 v h) (hints_cons _ _ _ (der_28083 v h) (hints_cons _ _ _ (der_28084 v h) (hints_cons _ _ _ (der_28085 v h) (hints_cons _ _ _ (der_28086 v h) (hints_cons _ _ _ (der_28087 v h) (hints_cons _ _ _ (der_28088 v h) (hints_cons _ _ _ (der_28089 v h) (hints_cons _ _ _ (der_28090 v h) (hints_cons _ _ _ (der_28091 v h) (hints_cons _ _ _ (der_28092 v h) (hints_cons _ _ _ (der_28093 v h) (hints_cons _ _ _ (der_28094 v h) (hints_cons _ _ _ (der_28095 v h) (hints_cons _ _ _ (der_28096 v h) (hints_cons _ _ _ (der_28097 v h) (hints_cons _ _ _ (der_28098 v h) (hints_cons _ _ _ (der_28100 v h) (hints_cons _ _ _ (der_28102 v h) (hints_cons _ _ _ (der_28104 v h) (hints_cons _ _ _ (der_28105 v h) (hints_cons _ _ _ (der_28106 v h) (hints_cons _ _ _ (der_28107 v h) (hints_cons _ _ _ (der_28108 v h) (hints_cons _ _ _ (der_28109 v h) (hints_cons _ _ _ (der_28110 v h) (hints_cons _ _ _ (der_28111 v h) (hints_cons _ _ _ (der_28112 v h) (hints_cons _ _ _ (der_28113 v h) (hints_cons _ _ _ (der_28114 v h) (hints_cons _ _ _ (der_28115 v h) (hints_cons _ _ _ (der_28116 v h) (hints_cons _ _ _ (der_28117 v h) (hints_cons _ _ _ (der_28118 v h) (hints_cons _ _ _ (der_28119 v h) (hints_cons _ _ _ (der_28120 v h) (hints_cons _ _ _ (der_28121 v h) (hints_cons _ _ _ (der_28122 v h) (hints_cons _ _ _ (der_28123 v h) (hints_cons _ _ _ (der_28124 v h) (hints_cons _ _ _ (der_28125 v h) (hints_cons _ _ _ (der_28126 v h) (hints_cons _ _ _ (der_28127 v h) (hints_cons _ _ _ (der_28128 v h) (hints_cons _ _ _ (der_28129 v h) (hints_cons _ _ _ (der_28130 v h) (hints_cons _ _ _ (der_28131 v h) (hints_cons _ _ _ (der_28132 v h) (hints_cons _ _ _ (der_28133 v h) (hints_cons _ _ _ (der_28134 v h) (hints_cons _ _ _ (der_28135 v h) (hints_cons _ _ _ (der_28136 v h) (hints_cons _ _ _ (der_28137 v h) (hints_cons _ _ _ (der_28138 v h) (hints_cons _ _ _ (der_28139 v h) (hints_cons _ _ _ (der_28140 v h) (hints_cons _ _ _ (der_28141 v h) (hints_cons _ _ _ (der_28142 v h) (hints_cons _ _ _ (der_28143 v h) (hints_cons _ _ _ (der_28144 v h) (hints_cons _ _ _ (der_28145 v h) (hints_cons _ _ _ (der_28146 v h) (hints_cons _ _ _ (der_28147 v h) (hints_cons _ _ _ (der_28148 v h) (hints_cons _ _ _ (der_28149 v h) (hints_cons _ _ _ (der_28150 v h) (hints_cons _ _ _ (der_28151 v h) (hints_cons _ _ _ (der_28152 v h) (hints_cons _ _ _ (der_28153 v h) (hints_cons _ _ _ (der_28154 v h) (hints_cons _ _ _ (der_28155 v h) (hints_cons _ _ _ (der_28156 v h) (hints_cons _ _ _ (der_28157 v h) (hints_cons _ _ _ (der_28158 v h) (hints_cons _ _ _ (der_28159 v h) (hints_cons _ _ _ (der_28160 v h) (hints_cons _ _ _ (der_28161 v h) (hints_cons _ _ _ (der_28162 v h) (hints_cons _ _ _ (der_28163 v h) (hints_cons _ _ _ (der_28164 v h) (hints_cons _ _ _ (der_28165 v h) (hints_cons _ _ _ (der_28166 v h) (hints_cons _ _ _ (der_28167 v h) (hints_cons _ _ _ (der_28168 v h) (hints_cons _ _ _ (der_28169 v h) (hints_cons _ _ _ (der_28170 v h) (hints_cons _ _ _ (der_28171 v h) (hints_cons _ _ _ (der_28172 v h) (hints_cons _ _ _ (der_28173 v h) (hints_cons _ _ _ (der_28174 v h) (hints_cons _ _ _ (der_28175 v h) (hints_cons _ _ _ (der_28176 v h) (hints_cons _ _ _ (der_28177 v h) (hints_cons _ _ _ (der_28178 v h) (hints_cons _ _ _ (der_28179 v h) (hints_cons _ _ _ (der_28180 v h) (hints_cons _ _ _ (der_28181 v h) (hints_cons _ _ _ (der_28182 v h) (hints_cons _ _ _ (der_28183 v h) (hints_cons _ _ _ (der_28184 v h) (hints_cons _ _ _ (der_28185 v h) (hints_cons _ _ _ (der_28186 v h) (hints_cons _ _ _ (der_28187 v h) (hints_cons _ _ _ (der_28188 v h) (hints_cons _ _ _ (der_28189 v h) (hints_cons _ _ _ (der_28190 v h) (hints_cons _ _ _ (der_28191 v h) (hints_cons _ _ _ (der_28192 v h) (hints_cons _ _ _ (der_28193 v h) (hints_cons _ _ _ (der_28194 v h) (hints_cons _ _ _ (der_28195 v h) (hints_cons _ _ _ (der_28196 v h) (hints_cons _ _ _ (der_28197 v h) (hints_cons _ _ _ (der_28198 v h) (hints_cons _ _ _ (der_28199 v h) (hints_cons _ _ _ (der_28200 v h) (hints_cons _ _ _ (der_28201 v h) (hints_cons _ _ _ (der_28202 v h) (hints_cons _ _ _ (der_28203 v h) (hints_cons _ _ _ (der_28204 v h) (hints_cons _ _ _ (der_28205 v h) (hints_cons _ _ _ (der_28206 v h) (hints_cons _ _ _ (der_28207 v h) (hints_cons _ _ _ (der_28208 v h) (hints_cons _ _ _ (der_28209 v h) (hints_cons _ _ _ (der_28210 v h) (hints_cons _ _ _ (der_28211 v h) (hints_cons _ _ _ (der_28212 v h) (hints_cons _ _ _ (der_28213 v h) (hints_cons _ _ _ (der_28214 v h) (hints_cons _ _ _ (der_28215 v h) (hints_cons _ _ _ (der_28216 v h) (hints_cons _ _ _ (der_28218 v h) (hints_cons _ _ _ (der_28219 v h) (hints_cons _ _ _ (der_28220 v h) (hints_cons _ _ _ (der_28221 v h) (hints_cons _ _ _ (der_28222 v h) (hints_cons _ _ _ (der_28223 v h) (hints_cons _ _ _ (der_28224 v h) (hints_cons _ _ _ (der_28225 v h) (hints_cons _ _ _ (der_28226 v h) (hints_cons _ _ _ (der_28227 v h) (hints_cons _ _ _ (der_28228 v h) (hints_cons _ _ _ (der_28229 v h) (hints_cons _ _ _ (der_28230 v h) (hints_cons _ _ _ (der_28231 v h) (hints_cons _ _ _ (der_28232 v h) (hints_cons _ _ _ (der_28233 v h) (hints_cons _ _ _ (der_28234 v h) (hints_cons _ _ _ (der_28235 v h) (hints_cons _ _ _ (der_28236 v h) (hints_cons _ _ _ (der_28237 v h) (hints_cons _ _ _ (der_28238 v h) (hints_cons _ _ _ (der_28239 v h) (hints_cons _ _ _ (der_28240 v h) (hints_cons _ _ _ (der_28241 v h) (hints_cons _ _ _ (der_28242 v h) (hints_cons _ _ _ (der_28243 v h) (hints_cons _ _ _ (der_28244 v h) (hints_cons _ _ _ (der_28245 v h) (hints_cons _ _ _ (der_28246 v h) (hints_cons _ _ _ (der_28247 v h) (hints_cons _ _ _ (der_28248 v h) (hints_cons _ _ _ (der_28249 v h) (hints_cons _ _ _ (der_28250 v h) (hints_cons _ _ _ (der_28251 v h) (hints_cons _ _ _ (der_28252 v h) (hints_cons _ _ _ (der_28253 v h) (hints_cons _ _ _ (der_28254 v h) (hints_cons _ _ _ (der_28255 v h) (hints_cons _ _ _ (der_28256 v h) (hints_cons _ _ _ (der_28257 v h) (hints_cons _ _ _ (der_28258 v h) (hints_cons _ _ _ (der_28259 v h) (hints_cons _ _ _ (der_28260 v h) (hints_cons _ _ _ (der_28261 v h) (hints_cons _ _ _ (der_28262 v h) (hints_cons _ _ _ (der_28263 v h) (hints_cons _ _ _ (der_28264 v h) (hints_cons _ _ _ (der_28265 v h) (hints_cons _ _ _ (der_28266 v h) (hints_cons _ _ _ (der_28267 v h) (hints_cons _ _ _ (der_28268 v h) (hints_cons _ _ _ (der_28269 v h) (hints_cons _ _ _ (der_28270 v h) (hints_cons _ _ _ (der_28271 v h) (hints_cons _ _ _ (der_28272 v h) (hints_cons _ _ _ (der_28273 v h) (hints_cons _ _ _ (der_28274 v h) (hints_cons _ _ _ (der_28275 v h) (hints_cons _ _ _ (der_28276 v h) (hints_cons _ _ _ (der_28277 v h) (hints_cons _ _ _ (der_28278 v h) (hints_cons _ _ _ (der_28279 v h) (hints_cons _ _ _ (der_28280 v h) (hints_cons _ _ _ (der_28281 v h) (hints_cons _ _ _ (der_28282 v h) (hints_cons _ _ _ (der_28283 v h) (hints_cons _ _ _ (der_28284 v h) (hints_cons _ _ _ (der_28285 v h) (hints_cons _ _ _ (der_28286 v h) (hints_cons _ _ _ (der_28287 v h) (hints_cons _ _ _ (der_28288 v h) (hints_cons _ _ _ (der_28289 v h) (hints_cons _ _ _ (der_28290 v h) (hints_cons _ _ _ (der_28291 v h) (hints_cons _ _ _ (der_28292 v h) (hints_cons _ _ _ (der_28293 v h) (hints_cons _ _ _ (der_28294 v h) (hints_cons _ _ _ (der_28295 v h) (hints_cons _ _ _ (der_28296 v h) (hints_cons _ _ _ (der_28297 v h) (hints_cons _ _ _ (der_28298 v h) (hints_cons _ _ _ (der_28299 v h) (hints_cons _ _ _ (der_28300 v h) (hints_cons _ _ _ (der_28301 v h) (hints_cons _ _ _ (der_28302 v h) (hints_cons _ _ _ (der_28303 v h) (hints_cons _ _ _ (der_28304 v h) (hints_cons _ _ _ (der_28305 v h) (hints_cons _ _ _ (der_28306 v h) (hints_cons _ _ _ (der_28307 v h) (hints_cons _ _ _ (der_28308 v h) (hints_cons _ _ _ (der_28309 v h) (hints_cons _ _ _ (der_28310 v h) (hints_cons _ _ _ (der_28311 v h) (hints_cons _ _ _ (der_28312 v h) (hints_cons _ _ _ (der_28313 v h) (hints_cons _ _ _ (der_28314 v h) (hints_cons _ _ _ (der_28315 v h) (hints_cons _ _ _ (der_28316 v h) (hints_cons _ _ _ (der_28317 v h) (hints_cons _ _ _ (der_28318 v h) (hints_cons _ _ _ (der_28319 v h) (hints_cons _ _ _ (der_28320 v h) (hints_cons _ _ _ (der_28321 v h) (hints_cons _ _ _ (der_28322 v h) (hints_cons _ _ _ (der_28323 v h) (hints_cons _ _ _ (der_28324 v h) (hints_cons _ _ _ (der_28325 v h) (hints_cons _ _ _ (der_28326 v h) (hints_cons _ _ _ (der_28327 v h) (hints_cons _ _ _ (der_28328 v h) (hints_cons _ _ _ (der_28329 v h) (hints_cons _ _ _ (der_28330 v h) (hints_cons _ _ _ (der_28331 v h) (hints_cons _ _ _ (der_28332 v h) (hints_cons _ _ _ (der_28333 v h) (hints_cons _ _ _ (der_28334 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix011 := prefix010 ++ chunk011
theorem prefix_sound011 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix011, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound010 v h c hc
  · exact chunk_sound011 v h c hc
end Percolation.NReplay
