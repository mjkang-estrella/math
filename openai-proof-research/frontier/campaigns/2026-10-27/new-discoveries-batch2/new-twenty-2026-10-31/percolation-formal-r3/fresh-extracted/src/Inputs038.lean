import Inputs037
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_6452 : CNF.NClause := [(50,false),(19,true),(63,true),(71,false),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6452 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6452 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6452 (by decide) v h
def cl_6454 : CNF.NClause := [(50,false),(19,true),(63,false),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6454 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6454 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6454 (by decide) v h
def cl_6456 : CNF.NClause := [(50,false),(19,true),(63,true),(71,true),(74,false),(77,true),(85,true),(90,false)]
theorem inp_6456 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6456 := by
  exact input_gate (spreadGate5 19) (spread_mem 19) cl_6456 (by decide) v h
def cl_6533 : CNF.NClause := [(51,false),(20,false),(67,false),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6533 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6533 := by
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6533 (by decide) v h
def cl_6534 : CNF.NClause := [(51,false),(20,true),(67,false),(68,true),(69,false),(70,false),(71,false),(92,false)]
theorem inp_6534 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6534 := by
  exact input_gate (spreadGate5 20) (spread_mem 20) cl_6534 (by decide) v h
def cl_6658 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,false),(88,false)]
theorem inp_6658 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6658 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6658 (by decide) v h
def cl_6666 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,false),(88,false)]
theorem inp_6666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6666 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6666 (by decide) v h
def cl_6674 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,false),(88,false)]
theorem inp_6674 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6674 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6674 (by decide) v h
def cl_6682 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,false),(88,false)]
theorem inp_6682 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6682 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6682 (by decide) v h
def cl_6690 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,true),(88,false)]
theorem inp_6690 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6690 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6690 (by decide) v h
def cl_6698 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,true),(88,false)]
theorem inp_6698 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6698 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6698 (by decide) v h
def cl_6706 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,true),(88,false)]
theorem inp_6706 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6706 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6706 (by decide) v h
def cl_6722 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,false),(88,true)]
theorem inp_6722 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6722 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6722 (by decide) v h
def cl_6730 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,false),(85,false),(88,true)]
theorem inp_6730 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6730 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6730 (by decide) v h
def cl_6738 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,true),(85,false),(88,true)]
theorem inp_6738 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6738 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6738 (by decide) v h
def cl_6746 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,true),(79,true),(85,false),(88,true)]
theorem inp_6746 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6746 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6746 (by decide) v h
def cl_6754 : CNF.NClause := [(52,false),(21,true),(66,false),(67,false),(73,false),(79,false),(85,true),(88,true)]
theorem inp_6754 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6754 := by
  exact input_gate (spreadGate5 21) (spread_mem 21) cl_6754 (by decide) v h
def cl_6786 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6786 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6786 := by
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6786 (by decide) v h
def cl_6790 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,false),(86,false),(90,false)]
theorem inp_6790 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6790 := by
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6790 (by decide) v h
def cl_6802 : CNF.NClause := [(53,false),(22,true),(64,false),(67,false),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6802 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6802 := by
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6802 (by decide) v h
def cl_6806 : CNF.NClause := [(53,false),(22,true),(64,false),(67,true),(75,false),(78,true),(86,false),(90,false)]
theorem inp_6806 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6806 := by
  exact input_gate (spreadGate5 22) (spread_mem 22) cl_6806 (by decide) v h
def cl_6913 : CNF.NClause := [(54,true),(23,false),(65,false),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6913 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6913 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6913 (by decide) v h
def cl_6914 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6914 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6914 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6914 (by decide) v h
def cl_6915 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6915 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6915 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6915 (by decide) v h
def cl_6916 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,false),(89,false)]
theorem inp_6916 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6916 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6916 (by decide) v h
def cl_6921 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,false),(89,false)]
theorem inp_6921 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6921 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6921 (by decide) v h
def cl_6929 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6929 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6929 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6929 (by decide) v h
def cl_6930 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,false),(89,false)]
theorem inp_6930 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6930 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6930 (by decide) v h
def cl_6946 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6946 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6946 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6946 (by decide) v h
def cl_6948 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,true),(89,false)]
theorem inp_6948 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6948 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6948 (by decide) v h
def cl_6962 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6962 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6962 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6962 (by decide) v h
def cl_6964 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,true),(89,false)]
theorem inp_6964 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6964 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6964 (by decide) v h
def cl_6977 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6977 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6977 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6977 (by decide) v h
def cl_6978 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6978 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6978 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6978 (by decide) v h
def cl_6979 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6979 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6979 (by decide) v h
def cl_6980 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,false),(89,true)]
theorem inp_6980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6980 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6980 (by decide) v h
def cl_6985 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,true),(81,false),(83,false),(89,true)]
theorem inp_6985 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6985 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6985 (by decide) v h
def cl_6993 : CNF.NClause := [(54,false),(23,false),(65,false),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6993 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6993 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6993 (by decide) v h
def cl_6994 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6994 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6994 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6994 (by decide) v h
def cl_6995 : CNF.NClause := [(54,false),(23,false),(65,true),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6995 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6995 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6995 (by decide) v h
def cl_6996 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,false),(89,true)]
theorem inp_6996 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_6996 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_6996 (by decide) v h
def cl_7010 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7010 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7010 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7010 (by decide) v h
def cl_7012 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,false),(83,true),(89,true)]
theorem inp_7012 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7012 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7012 (by decide) v h
def cl_7026 : CNF.NClause := [(54,false),(23,true),(65,false),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7026 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7026 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7026 (by decide) v h
def cl_7028 : CNF.NClause := [(54,false),(23,true),(65,true),(67,false),(74,false),(81,true),(83,true),(89,true)]
theorem inp_7028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7028 := by
  exact input_gate (spreadGate5 23) (spread_mem 23) cl_7028 (by decide) v h
def cl_7041 : CNF.NClause := [(55,true),(24,false),(63,false),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7041 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7041 := by
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7041 (by decide) v h
def cl_7043 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7043 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7043 := by
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7043 (by decide) v h
def cl_7044 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,false),(80,false),(84,false),(91,false)]
theorem inp_7044 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7044 := by
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7044 (by decide) v h
def cl_7050 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7050 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7050 := by
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7050 (by decide) v h
def cl_7052 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(76,true),(80,false),(84,false),(91,false)]
theorem inp_7052 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_7052 := by
  exact input_gate (spreadGate5 24) (spread_mem 24) cl_7052 (by decide) v h
end Percolation.Replay
