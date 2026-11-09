import Tree28_002
set_option exponentiation.threshold 200000
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
open Schrijver
example : treeCheck 3185 maskAt28 Tree28_002.parents Tree28_002.depths Tree28_002.root 5 = true := by decide
