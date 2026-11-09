import Magic
set_option warningAsError true
open Magic381805
example : vertexLabel 6 = 1 := by decide
example : ¬G.Adj 0 2 := by decide
example : ¬IsSuperEdgeMagic G 11 11 27 labelEquiv := by unfold IsSuperEdgeMagic; decide
