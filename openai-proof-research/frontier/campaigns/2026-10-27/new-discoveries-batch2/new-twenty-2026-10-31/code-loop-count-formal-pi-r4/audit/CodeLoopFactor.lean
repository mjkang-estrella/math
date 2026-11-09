import CodeLoopFactor

/-!
Dedicated axiom audit for every production declaration of `CodeLoopFactor`
(the 26 declarations of the copied verified source, SHA256
73b81dd94eadf2d12ac03caf962ff6bfc904f8189f0d84e51a62eee0ecccad9d).
Printed output is the unabridged kernel axiom set per declaration; the run
log is preserved and hashed.  Only `propext`, `Classical.choice`,
`Quot.sound` may appear.
-/

#print axioms codeLoopF
#print axioms codeLoopQ
#print axioms codeLoopF_zero_left
#print axioms codeLoopF_zero_right
#print axioms zmod2_val_one
#print axioms zmod2_cases
#print axioms zmod2_mul_self
#print axioms zmod2_add_self
#print axioms zmod2_one_add
#print axioms codeLoopF_self
#print axioms codeLoopF_symmetry
#print axioms codeLoopF_coboundary
#print axioms W4
#print axioms W3
#print axioms e4v
#print axioms e3v
#print axioms dot4
#print axioms dot3
#print axioms dot4_add_left
#print axioms dot3_add_left
#print axioms dot4_add_right
#print axioms dot4_zero_left
#print axioms dot3_zero_left
#print axioms card_W4
#print axioms card_W3
#print axioms exists_one_of_ne_zero4
