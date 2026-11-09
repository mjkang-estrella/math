import NInputs011
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_844 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,false),(26,false)]
theorem inp_844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_844 v hb
def cl_845 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,false),(26,false)]
theorem inp_845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_845 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_845 (by decide) v hb
def cl_846 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,false),(26,false)]
theorem inp_846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_846 v hb
def cl_847 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,false),(26,false)]
theorem inp_847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_847 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_847 v hb
def cl_848 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,true),(22,false),(26,false)]
theorem inp_848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_848 v hb
def cl_849 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,true),(26,false)]
theorem inp_849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_849 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_849 (by decide) v hb
def cl_850 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,true),(26,false)]
theorem inp_850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_850 (by decide) v hb
def cl_851 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,true),(26,false)]
theorem inp_851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_851 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_851 v hb
def cl_852 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,true),(26,false)]
theorem inp_852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_852 (by decide) v hb
def cl_853 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,true),(26,false)]
theorem inp_853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_853 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_853 v hb
def cl_854 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,true),(26,false)]
theorem inp_854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_854 v hb
def cl_855 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,true),(26,false)]
theorem inp_855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_855 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_855 v hb
def cl_856 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,true),(26,false)]
theorem inp_856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_856 (by decide) v hb
def cl_857 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,true),(26,false)]
theorem inp_857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_857 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_857 (by decide) v hb
def cl_858 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,true),(26,false)]
theorem inp_858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_858 (by decide) v hb
def cl_859 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,true),(26,false)]
theorem inp_859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_859 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_859 v hb
def cl_860 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,true),(26,false)]
theorem inp_860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_860 (by decide) v hb
def cl_861 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,true),(26,false)]
theorem inp_861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_861 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_861 (by decide) v hb
def cl_862 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,true),(26,false)]
theorem inp_862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_862 v hb
def cl_863 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,true),(26,false)]
theorem inp_863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_863 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_863 v hb
def cl_864 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,true),(22,true),(26,false)]
theorem inp_864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_864 (by decide) v hb
def cl_865 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,false),(26,true)]
theorem inp_865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_865 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_865 v hb
def cl_866 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,false),(26,true)]
theorem inp_866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_866 (by decide) v hb
def cl_867 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,false),(26,true)]
theorem inp_867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_867 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_867 v hb
def cl_868 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,false),(26,true)]
theorem inp_868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_868 v hb
def cl_869 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,false),(26,true)]
theorem inp_869 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_869 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_869 (by decide) v hb
def cl_870 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,false),(26,true)]
theorem inp_870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_870 (by decide) v hb
def cl_871 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,false),(26,true)]
theorem inp_871 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_871 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_871 v hb
def cl_872 : CNF.NClause := [(75,true),(3,true),(9,true),(10,true),(16,false),(22,false),(26,true)]
theorem inp_872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_872 v hb
def cl_873 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,false),(26,true)]
theorem inp_873 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_873 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_873 (by decide) v hb
def cl_874 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,false),(26,true)]
theorem inp_874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_874 (by decide) v hb
def cl_875 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,false),(26,true)]
theorem inp_875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_875 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_875 v hb
def cl_876 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,true),(22,false),(26,true)]
theorem inp_876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_876 v hb
def cl_877 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,false),(26,true)]
theorem inp_877 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_877 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_877 (by decide) v hb
def cl_878 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,true),(22,false),(26,true)]
theorem inp_878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_878 (by decide) v hb
def cl_879 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,true),(22,false),(26,true)]
theorem inp_879 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_879 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_879 v hb
def cl_880 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,true),(22,false),(26,true)]
theorem inp_880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_880 (by decide) v hb
def cl_881 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,false),(22,true),(26,true)]
theorem inp_881 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_881 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_881 (by decide) v hb
def cl_882 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,false),(22,true),(26,true)]
theorem inp_882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_882 (by decide) v hb
def cl_883 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,false),(22,true),(26,true)]
theorem inp_883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_883 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_883 v hb
def cl_884 : CNF.NClause := [(75,true),(3,true),(9,true),(10,false),(16,false),(22,true),(26,true)]
theorem inp_884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_884 (by decide) v hb
def cl_885 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,false),(22,true),(26,true)]
theorem inp_885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_885 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_885 (by decide) v hb
def cl_886 : CNF.NClause := [(75,true),(3,true),(9,false),(10,true),(16,false),(22,true),(26,true)]
theorem inp_886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_886 (by decide) v hb
def cl_887 : CNF.NClause := [(75,true),(3,false),(9,true),(10,true),(16,false),(22,true),(26,true)]
theorem inp_887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_887 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_887 v hb
def cl_888 : CNF.NClause := [(75,false),(3,true),(9,true),(10,true),(16,false),(22,true),(26,true)]
theorem inp_888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_888 (by decide) v hb
def cl_889 : CNF.NClause := [(75,true),(3,false),(9,false),(10,false),(16,true),(22,true),(26,true)]
theorem inp_889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_889 (by decide) v hb
def cl_890 : CNF.NClause := [(75,true),(3,true),(9,false),(10,false),(16,true),(22,true),(26,true)]
theorem inp_890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_890 (by decide) v hb
def cl_891 : CNF.NClause := [(75,true),(3,false),(9,true),(10,false),(16,true),(22,true),(26,true)]
theorem inp_891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_891 v hb
def cl_892 : CNF.NClause := [(75,false),(3,true),(9,true),(10,false),(16,true),(22,true),(26,true)]
theorem inp_892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_892 (by decide) v hb
def cl_893 : CNF.NClause := [(75,true),(3,false),(9,false),(10,true),(16,true),(22,true),(26,true)]
theorem inp_893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_893 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.a (.i 13) 13) (activationA_mem 13) cl_893 (by decide) v hb
end Percolation.NReplay
