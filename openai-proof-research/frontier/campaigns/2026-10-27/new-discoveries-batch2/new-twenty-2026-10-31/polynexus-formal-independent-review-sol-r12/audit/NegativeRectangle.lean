import PolynexusLiteral
example : PBlk 2 0 0 1 (0 : Fin 2) (1 : Fin 2) = 1 := by
  norm_num [PBlk, PCnd]
