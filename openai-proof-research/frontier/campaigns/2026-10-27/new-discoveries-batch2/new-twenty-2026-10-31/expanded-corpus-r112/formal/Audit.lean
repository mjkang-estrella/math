import CycMain
open CycRamsey
#check @cycRamsey_startStar_monPath
#print axioms cycRamsey_startStar_monPath
#print axioms theoremA
#print axioms upper
#print axioms no_red_star
#print axioms no_blue_path
#print axioms rot_embedding
#print CycRamsey.IsCyclicEmbedding
#print CycRamsey.ContainsCyc
#print CycRamsey.CycRamseyProp
#print CycRamsey.cycRamsey
#print CycRamsey.startStar
#print CycRamsey.monPath
-- sanity: small instances of the definitions
example : (startStar 3).Adj ⟨0, by omega⟩ ⟨2, by omega⟩ := by
  rw [startStar, SimpleGraph.fromRel_adj]; decide
example : ¬ (monPath 4).Adj ⟨0, by omega⟩ ⟨2, by omega⟩ := by
  rw [monPath, SimpleGraph.fromRel_adj]; decide
example : cycRamsey (startStar 3) (monPath 4) = 5 := cycRamsey_startStar_monPath 3 4 le_rfl le_rfl
