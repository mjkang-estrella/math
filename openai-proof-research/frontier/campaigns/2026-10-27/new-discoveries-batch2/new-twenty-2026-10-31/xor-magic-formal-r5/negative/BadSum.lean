import Base16Closed4
example : ∀ v, (∑ u ∈ XorMagic.Base16Closed4.graph.neighborFinset v, XorMagic.Base16Closed4.labels u) = 0 := by decide
