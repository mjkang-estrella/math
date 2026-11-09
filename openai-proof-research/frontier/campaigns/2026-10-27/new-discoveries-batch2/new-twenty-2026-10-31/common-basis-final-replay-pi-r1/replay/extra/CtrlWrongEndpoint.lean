import Final
-- WRONG-endpoint negative control: asserts the two deleted ground elements of the
-- CommonBasis332371 endpoint (1 and 6 in Fin 9) are equal. False; must fail.
theorem ctrlWrongEndpoint : (1 : Fin 9) = 6 := by decide
