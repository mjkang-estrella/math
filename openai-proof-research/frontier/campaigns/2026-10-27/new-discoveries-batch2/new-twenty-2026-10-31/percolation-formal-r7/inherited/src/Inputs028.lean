import Inputs027
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2861 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false),(57,true)]
theorem inp_2861 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2861 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2861 (by decide) v h
def cl_2862 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,false),(57,true)]
theorem inp_2862 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2862 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2862 (by decide) v h
def cl_2871 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,true),(57,true)]
theorem inp_2871 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2871 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2871 (by decide) v h
def cl_2874 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,true),(57,true)]
theorem inp_2874 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2874 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2874 (by decide) v h
def cl_2877 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,true),(57,true)]
theorem inp_2877 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2877 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2877 (by decide) v h
def cl_2881 : CNF.NClause := [(107,true),(32,false),(39,false),(41,false),(48,false),(55,false),(58,false)]
theorem inp_2881 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2881 := by
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2881 (by decide) v h
def cl_2885 : CNF.NClause := [(107,true),(32,false),(39,false),(41,true),(48,false),(55,false),(58,false)]
theorem inp_2885 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2885 := by
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2885 (by decide) v h
def cl_2903 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,true),(58,false)]
theorem inp_2903 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2903 := by
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2903 (by decide) v h
def cl_2919 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,false),(58,true)]
theorem inp_2919 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2919 := by
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2919 (by decide) v h
def cl_2920 : CNF.NClause := [(107,true),(32,true),(39,true),(41,true),(48,false),(55,false),(58,true)]
theorem inp_2920 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2920 := by
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2920 (by decide) v h
def cl_2935 : CNF.NClause := [(107,true),(32,false),(39,true),(41,true),(48,false),(55,true),(58,true)]
theorem inp_2935 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2935 := by
  exact input_gate (activationGate5 SatVar.x (.j 14) 14) (activationX_mem 14) cl_2935 (by decide) v h
def cl_2945 : CNF.NClause := [(108,true),(46,false),(47,false),(48,false),(49,false),(50,false),(61,false)]
theorem inp_2945 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2945 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2945 (by decide) v h
def cl_2946 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false),(49,false),(50,false),(61,false)]
theorem inp_2946 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2946 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2946 (by decide) v h
def cl_2979 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,false),(61,true)]
theorem inp_2979 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2979 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2979 (by decide) v h
def cl_2980 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,false),(61,true)]
theorem inp_2980 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2980 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2980 (by decide) v h
def cl_2983 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,false),(61,true)]
theorem inp_2983 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2983 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2983 (by decide) v h
def cl_2984 : CNF.NClause := [(108,true),(46,true),(47,true),(48,true),(49,false),(50,false),(61,true)]
theorem inp_2984 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2984 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2984 (by decide) v h
def cl_2987 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,true),(50,false),(61,true)]
theorem inp_2987 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2987 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2987 (by decide) v h
def cl_2991 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,true),(50,false),(61,true)]
theorem inp_2991 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2991 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2991 (by decide) v h
def cl_2995 : CNF.NClause := [(108,true),(46,false),(47,true),(48,false),(49,false),(50,true),(61,true)]
theorem inp_2995 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2995 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2995 (by decide) v h
def cl_2996 : CNF.NClause := [(108,true),(46,true),(47,true),(48,false),(49,false),(50,true),(61,true)]
theorem inp_2996 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2996 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2996 (by decide) v h
def cl_2999 : CNF.NClause := [(108,true),(46,false),(47,true),(48,true),(49,false),(50,true),(61,true)]
theorem inp_2999 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2999 := by
  exact input_gate (activationGate5 SatVar.x (.j 15) 15) (activationX_mem 15) cl_2999 (by decide) v h
def cl_3028 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,true),(58,false)]
theorem inp_3028 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3028 := by
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3028 (by decide) v h
def cl_3059 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,false),(53,true),(58,true)]
theorem inp_3059 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3059 := by
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3059 (by decide) v h
def cl_3060 : CNF.NClause := [(109,true),(35,true),(37,true),(44,false),(46,false),(53,true),(58,true)]
theorem inp_3060 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3060 := by
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3060 (by decide) v h
def cl_3063 : CNF.NClause := [(109,true),(35,false),(37,true),(44,true),(46,false),(53,true),(58,true)]
theorem inp_3063 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3063 := by
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3063 (by decide) v h
def cl_3067 : CNF.NClause := [(109,true),(35,false),(37,true),(44,false),(46,true),(53,true),(58,true)]
theorem inp_3067 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3067 := by
  exact input_gate (activationGate5 SatVar.x (.j 16) 16) (activationX_mem 16) cl_3067 (by decide) v h
def cl_3073 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,false),(57,false)]
theorem inp_3073 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3073 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3073 (by decide) v h
def cl_3074 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,false),(52,false),(57,false)]
theorem inp_3074 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3074 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3074 (by decide) v h
def cl_3082 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,false),(57,false)]
theorem inp_3082 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3082 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3082 (by decide) v h
def cl_3098 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,true),(57,false)]
theorem inp_3098 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3098 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3098 (by decide) v h
def cl_3114 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,false),(57,true)]
theorem inp_3114 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3114 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3114 (by decide) v h
def cl_3121 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3121 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3121 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3121 (by decide) v h
def cl_3123 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3123 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3123 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3123 (by decide) v h
def cl_3124 : CNF.NClause := [(110,true),(33,true),(39,true),(45,false),(46,false),(52,true),(57,true)]
theorem inp_3124 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3124 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3124 (by decide) v h
def cl_3127 : CNF.NClause := [(110,true),(33,false),(39,true),(45,true),(46,false),(52,true),(57,true)]
theorem inp_3127 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3127 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3127 (by decide) v h
def cl_3129 : CNF.NClause := [(110,true),(33,false),(39,false),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3129 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3129 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3129 (by decide) v h
def cl_3130 : CNF.NClause := [(110,true),(33,true),(39,false),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3130 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3130 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3130 (by decide) v h
def cl_3131 : CNF.NClause := [(110,true),(33,false),(39,true),(45,false),(46,true),(52,true),(57,true)]
theorem inp_3131 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3131 := by
  exact input_gate (activationGate5 SatVar.x (.j 17) 17) (activationX_mem 17) cl_3131 (by decide) v h
def cl_3137 : CNF.NClause := [(111,true),(34,false),(38,false),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3137 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3137 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3137 (by decide) v h
def cl_3139 : CNF.NClause := [(111,true),(34,false),(38,true),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3139 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3139 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3139 (by decide) v h
def cl_3140 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,false),(60,false)]
theorem inp_3140 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3140 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3140 (by decide) v h
def cl_3143 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,false),(60,false)]
theorem inp_3143 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3143 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3143 (by decide) v h
def cl_3144 : CNF.NClause := [(111,true),(34,true),(38,true),(42,true),(46,false),(55,false),(60,false)]
theorem inp_3144 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3144 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3144 (by decide) v h
def cl_3148 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,false),(60,false)]
theorem inp_3148 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3148 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3148 (by decide) v h
def cl_3151 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,false),(60,false)]
theorem inp_3151 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3151 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3151 (by decide) v h
def cl_3156 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,false),(55,true),(60,false)]
theorem inp_3156 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3156 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3156 (by decide) v h
def cl_3159 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,false),(55,true),(60,false)]
theorem inp_3159 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3159 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3159 (by decide) v h
def cl_3164 : CNF.NClause := [(111,true),(34,true),(38,true),(42,false),(46,true),(55,true),(60,false)]
theorem inp_3164 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3164 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3164 (by decide) v h
def cl_3167 : CNF.NClause := [(111,true),(34,false),(38,true),(42,true),(46,true),(55,true),(60,false)]
theorem inp_3167 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_3167 := by
  exact input_gate (activationGate5 SatVar.x (.j 18) 18) (activationX_mem 18) cl_3167 (by decide) v h
end Percolation.Replay
