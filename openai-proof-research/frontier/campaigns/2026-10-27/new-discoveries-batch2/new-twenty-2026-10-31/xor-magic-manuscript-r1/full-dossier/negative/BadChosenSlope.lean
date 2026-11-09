import ColourSeed16Closed4
open XorMagic
example : outgoingSlope Base16Closed4.graph (chosenSlopes Base16Closed4.graph Seed16Closed4.colouring) 0 9 = 2 := by decide
