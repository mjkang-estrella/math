import NInputs137
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_7802 : CNF.NClause := [(60,false),(29,true),(62,false),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7802 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7802 (by decide) v hb
def cl_7803 : CNF.NClause := [(60,false),(29,false),(62,true),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7803 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7803 (by decide) v hb
def cl_7804 : CNF.NClause := [(60,false),(29,true),(62,true),(68,false),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7804 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7804 (by decide) v hb
def cl_7805 : CNF.NClause := [(60,false),(29,false),(62,false),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7805 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7805 (by decide) v hb
def cl_7806 : CNF.NClause := [(60,false),(29,true),(62,false),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7806 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7806 (by decide) v hb
def cl_7807 : CNF.NClause := [(60,false),(29,false),(62,true),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7807 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7807 (by decide) v hb
def cl_7808 : CNF.NClause := [(60,false),(29,true),(62,true),(68,true),(74,true),(80,true),(86,true),(88,true)]
theorem inp_7808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7808 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 29) (spread_mem 29) cl_7808 (by decide) v hb
def cl_7810 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,false),(87,false)]
theorem inp_7810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7810 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7810 (by decide) v hb
def cl_7812 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,false),(87,false)]
theorem inp_7812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7812 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7812 (by decide) v hb
def cl_7814 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,false),(87,false)]
theorem inp_7814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7814 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7814 (by decide) v hb
def cl_7816 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,false),(87,false)]
theorem inp_7816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7816 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7816 (by decide) v hb
def cl_7818 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,false),(87,false)]
theorem inp_7818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7818 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7818 (by decide) v hb
def cl_7820 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,false),(87,false)]
theorem inp_7820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7820 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7820 (by decide) v hb
def cl_7822 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,false),(87,false)]
theorem inp_7822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7822 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7822 (by decide) v hb
def cl_7824 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,false),(87,false)]
theorem inp_7824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7824 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7824 (by decide) v hb
def cl_7826 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,false),(87,false)]
theorem inp_7826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7826 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7826 (by decide) v hb
def cl_7828 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,false),(87,false)]
theorem inp_7828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7828 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7828 (by decide) v hb
def cl_7830 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,false),(87,false)]
theorem inp_7830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7830 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7830 (by decide) v hb
def cl_7832 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,false),(87,false)]
theorem inp_7832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7832 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7832 (by decide) v hb
def cl_7834 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,false),(87,false)]
theorem inp_7834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7834 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7834 (by decide) v hb
def cl_7836 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,false),(87,false)]
theorem inp_7836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7836 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7836 (by decide) v hb
def cl_7838 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,false),(87,false)]
theorem inp_7838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7838 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7838 (by decide) v hb
def cl_7840 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,false),(87,false)]
theorem inp_7840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7840 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7840 (by decide) v hb
def cl_7842 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,true),(87,false)]
theorem inp_7842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7842 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7842 v hb
def cl_7844 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,true),(87,false)]
theorem inp_7844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7844 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7844 v hb
def cl_7846 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,true),(87,false)]
theorem inp_7846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7846 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7846 (by decide) v hb
def cl_7848 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,true),(87,false)]
theorem inp_7848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7848 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7848 (by decide) v hb
def cl_7850 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,true),(87,false)]
theorem inp_7850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7850 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7850 v hb
def cl_7852 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,true),(87,false)]
theorem inp_7852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7852 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7852 v hb
def cl_7854 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,true),(87,false)]
theorem inp_7854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7854 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7854 (by decide) v hb
def cl_7856 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,true),(87,false)]
theorem inp_7856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7856 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7856 (by decide) v hb
def cl_7858 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,true),(87,false)]
theorem inp_7858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7858 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7858 v hb
def cl_7860 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,true),(87,false)]
theorem inp_7860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7860 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact Percolation.Replay.inp_7860 v hb
def cl_7862 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,true),(87,false)]
theorem inp_7862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7862 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7862 (by decide) v hb
def cl_7864 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,true),(82,true),(87,false)]
theorem inp_7864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7864 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7864 (by decide) v hb
def cl_7866 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,true),(82,true),(87,false)]
theorem inp_7866 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7866 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7866 (by decide) v hb
def cl_7868 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,true),(82,true),(87,false)]
theorem inp_7868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7868 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7868 (by decide) v hb
def cl_7870 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,true),(82,true),(87,false)]
theorem inp_7870 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7870 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7870 (by decide) v hb
def cl_7872 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,true),(82,true),(87,false)]
theorem inp_7872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7872 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7872 (by decide) v hb
def cl_7874 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,false),(82,false),(87,true)]
theorem inp_7874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7874 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7874 (by decide) v hb
def cl_7876 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,false),(82,false),(87,true)]
theorem inp_7876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7876 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7876 (by decide) v hb
def cl_7878 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,false),(82,false),(87,true)]
theorem inp_7878 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7878 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7878 (by decide) v hb
def cl_7880 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,false),(77,false),(82,false),(87,true)]
theorem inp_7880 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7880 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7880 (by decide) v hb
def cl_7882 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,true),(77,false),(82,false),(87,true)]
theorem inp_7882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7882 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7882 (by decide) v hb
def cl_7884 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,true),(77,false),(82,false),(87,true)]
theorem inp_7884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7884 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7884 (by decide) v hb
def cl_7886 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,true),(77,false),(82,false),(87,true)]
theorem inp_7886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7886 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7886 (by decide) v hb
def cl_7888 : CNF.NClause := [(61,false),(30,true),(62,true),(67,true),(72,true),(77,false),(82,false),(87,true)]
theorem inp_7888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7888 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7888 (by decide) v hb
def cl_7890 : CNF.NClause := [(61,false),(30,true),(62,false),(67,false),(72,false),(77,true),(82,false),(87,true)]
theorem inp_7890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7890 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7890 (by decide) v hb
def cl_7892 : CNF.NClause := [(61,false),(30,true),(62,true),(67,false),(72,false),(77,true),(82,false),(87,true)]
theorem inp_7892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7892 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7892 (by decide) v hb
def cl_7894 : CNF.NClause := [(61,false),(30,true),(62,false),(67,true),(72,false),(77,true),(82,false),(87,true)]
theorem inp_7894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7894 := by
  have hb : ∀ d ∈ inputCNF5, CNF.Holds v d := fun d hd => h d (List.mem_append_left _ hd)
  exact input_gate (spreadGate5 30) (spread_mem 30) cl_7894 (by decide) v hb
end Percolation.NReplay
