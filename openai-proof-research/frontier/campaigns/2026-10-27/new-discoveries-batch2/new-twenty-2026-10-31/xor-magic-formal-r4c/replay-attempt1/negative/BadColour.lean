import ColourSeed16Closed4
open XorMagic
example : Seed16Closed4.colouring.colour 0 = Seed16Closed4.colouring.colour (Seed16Closed4.decomposition0.mate 0 0) := by decide
