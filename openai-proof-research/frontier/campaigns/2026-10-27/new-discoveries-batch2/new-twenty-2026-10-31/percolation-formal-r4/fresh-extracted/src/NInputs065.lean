import NInputs064
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_3889 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,false),(55,true),(57,true)]
theorem inp_3889 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3889 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3889 (by decide) v hb
def cl_3890 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,false),(55,true),(57,true)]
theorem inp_3890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3890 (by decide) v hb
def cl_3891 : CNF.NClause := [(122,true),(31,false),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem inp_3891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3891 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3891 v hb
def cl_3892 : CNF.NClause := [(122,true),(31,true),(37,true),(43,false),(49,false),(55,true),(57,true)]
theorem inp_3892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3892 v hb
def cl_3894 : CNF.NClause := [(122,true),(31,true),(37,false),(43,true),(49,false),(55,true),(57,true)]
theorem inp_3894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3894 (by decide) v hb
def cl_3896 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,false),(55,true),(57,true)]
theorem inp_3896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3896 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3896 (by decide) v hb
def cl_3897 : CNF.NClause := [(122,true),(31,false),(37,false),(43,false),(49,true),(55,true),(57,true)]
theorem inp_3897 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3897 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3897 (by decide) v hb
def cl_3898 : CNF.NClause := [(122,true),(31,true),(37,false),(43,false),(49,true),(55,true),(57,true)]
theorem inp_3898 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3898 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3898 (by decide) v hb
def cl_3900 : CNF.NClause := [(122,false),(31,true),(37,true),(43,false),(49,true),(55,true),(57,true)]
theorem inp_3900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3900 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3900 (by decide) v hb
def cl_3902 : CNF.NClause := [(122,false),(31,true),(37,false),(43,true),(49,true),(55,true),(57,true)]
theorem inp_3902 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3902 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 29) 29) (activationX_mem 29) cl_3902 (by decide) v hb
def cl_3904 : CNF.NClause := [(122,false),(31,true),(37,true),(43,true),(49,true),(55,true),(57,true)]
theorem inp_3904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3904 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3904 v hb
def cl_3905 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,false),(56,false)]
theorem inp_3905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3905 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3905 (by decide) v hb
def cl_3906 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,false),(56,false)]
theorem inp_3906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3906 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3906 (by decide) v hb
def cl_3907 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,false),(56,false)]
theorem inp_3907 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3907 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3907 v hb
def cl_3908 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,false),(56,false)]
theorem inp_3908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3908 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3908 v hb
def cl_3909 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,false),(56,false)]
theorem inp_3909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3909 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3909 (by decide) v hb
def cl_3910 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,false),(56,false)]
theorem inp_3910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3910 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3910 (by decide) v hb
def cl_3911 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,false),(56,false)]
theorem inp_3911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3911 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3911 v hb
def cl_3912 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,false),(56,false)]
theorem inp_3912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3912 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3912 v hb
def cl_3913 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,false),(56,false)]
theorem inp_3913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3913 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3913 (by decide) v hb
def cl_3914 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,false),(56,false)]
theorem inp_3914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3914 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3914 (by decide) v hb
def cl_3915 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,true),(51,false),(56,false)]
theorem inp_3915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3915 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3915 v hb
def cl_3918 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,true),(51,false),(56,false)]
theorem inp_3918 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3918 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3918 (by decide) v hb
def cl_3919 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,true),(51,false),(56,false)]
theorem inp_3919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3919 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3919 v hb
def cl_3920 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,true),(51,false),(56,false)]
theorem inp_3920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3920 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3920 v hb
def cl_3921 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,true),(56,false)]
theorem inp_3921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3921 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3921 (by decide) v hb
def cl_3922 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,true),(56,false)]
theorem inp_3922 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3922 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3922 (by decide) v hb
def cl_3923 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,true),(56,false)]
theorem inp_3923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3923 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3923 v hb
def cl_3925 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,true),(56,false)]
theorem inp_3925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3925 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3925 (by decide) v hb
def cl_3926 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,true),(56,false)]
theorem inp_3926 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3926 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3926 (by decide) v hb
def cl_3927 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,true),(56,false)]
theorem inp_3927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3927 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3927 v hb
def cl_3928 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,true),(56,false)]
theorem inp_3928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3928 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3928 v hb
def cl_3929 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,true),(56,false)]
theorem inp_3929 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3929 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3929 (by decide) v hb
def cl_3930 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,true),(56,false)]
theorem inp_3930 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3930 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3930 (by decide) v hb
def cl_3934 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,true),(51,true),(56,false)]
theorem inp_3934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3934 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3934 (by decide) v hb
def cl_3936 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,true),(51,true),(56,false)]
theorem inp_3936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3936 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3936 (by decide) v hb
def cl_3937 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,false),(51,false),(56,true)]
theorem inp_3937 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3937 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3937 (by decide) v hb
def cl_3938 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,false),(51,false),(56,true)]
theorem inp_3938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3938 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3938 (by decide) v hb
def cl_3939 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,false),(51,false),(56,true)]
theorem inp_3939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3939 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3939 (by decide) v hb
def cl_3940 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,false),(51,false),(56,true)]
theorem inp_3940 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3940 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3940 (by decide) v hb
def cl_3941 : CNF.NClause := [(123,true),(31,false),(36,false),(41,true),(46,false),(51,false),(56,true)]
theorem inp_3941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3941 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3941 (by decide) v hb
def cl_3942 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,false),(51,false),(56,true)]
theorem inp_3942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3942 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3942 (by decide) v hb
def cl_3943 : CNF.NClause := [(123,true),(31,false),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem inp_3943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3943 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3943 v hb
def cl_3944 : CNF.NClause := [(123,true),(31,true),(36,true),(41,true),(46,false),(51,false),(56,true)]
theorem inp_3944 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3944 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_3944 v hb
def cl_3945 : CNF.NClause := [(123,true),(31,false),(36,false),(41,false),(46,true),(51,false),(56,true)]
theorem inp_3945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3945 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3945 (by decide) v hb
def cl_3946 : CNF.NClause := [(123,true),(31,true),(36,false),(41,false),(46,true),(51,false),(56,true)]
theorem inp_3946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3946 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3946 (by decide) v hb
def cl_3947 : CNF.NClause := [(123,true),(31,false),(36,true),(41,false),(46,true),(51,false),(56,true)]
theorem inp_3947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3947 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3947 (by decide) v hb
def cl_3948 : CNF.NClause := [(123,true),(31,true),(36,true),(41,false),(46,true),(51,false),(56,true)]
theorem inp_3948 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3948 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3948 (by decide) v hb
def cl_3950 : CNF.NClause := [(123,true),(31,true),(36,false),(41,true),(46,true),(51,false),(56,true)]
theorem inp_3950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3950 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3950 (by decide) v hb
def cl_3952 : CNF.NClause := [(123,false),(31,true),(36,true),(41,true),(46,true),(51,false),(56,true)]
theorem inp_3952 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3952 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (activationGate5 SatVar.x (.j 30) 30) (activationX_mem 30) cl_3952 (by decide) v hb
end Percolation.NReplay
