import PolynexusLiteral
example : PBlk 2 0 0 1 ⟨0,by omega⟩ ⟨1,by omega⟩ = 1 := by
  norm_num [PBlk, PCnd]
