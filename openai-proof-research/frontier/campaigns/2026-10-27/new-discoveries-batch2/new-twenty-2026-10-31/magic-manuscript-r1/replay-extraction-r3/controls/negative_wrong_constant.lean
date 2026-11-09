import Magic
set_option warningAsError true
open Magic381805
example : IsSuperEdgeMagic G 11 11 27 labelEquiv := by unfold IsSuperEdgeMagic; decide
