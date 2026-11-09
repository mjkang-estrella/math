# 343790 code-loop-factor lane — summary (in progress)

Stage 1 DONE: src/CodeLoopFactor.lean defines the reviewed factor
codeLoopF (Fin 3 -> ZMod 2, 9 monomials) and codeLoopQ, with genuine
all-input normalization theorems codeLoopF_zero_left/right; strict
check.sh compile exit 0 and checker.sh exit 0 (receipts+logs hashed in
results/343790-milestone-stage1.json).

Pending: all-input identities (f(x,x)=q(x); symmetry/coboundary 6-monomial
identity), then the full nonassociative code loop construction. Credit 0;
52/60 unchanged. No acceptance claimed.

Stage 2 DONE: all-input identities codeLoopF_self (f(x,x)=q(x)),
codeLoopF_symmetry, codeLoopF_coboundary (6-monomial alternating triple
form); proved for ALL inputs by coordinate case analysis (rcases
zmod2_cases cascades + decide). check.sh + checker.sh exit 0.
results/343790-milestone-stage2.json.

Stage 3ground DONE: ground types W4/W3 (Fin 4/3 -> ZMod 2), unit vectors,
dot products with add/zero lemmas, cardinalities card_W4=16 / card_W3=8,
nonzero-has-unit-coordinate lemma. check.sh + checker.sh exit 0;
results/343790-milestone-stage3ground.json.

Remaining: S3count (fiber parities, 4-divisibility, parity bridge, triple
character sum), S4 (43+7=50 coordinate type, subspace, injectivity), S5
(weights, factor axioms on codewords), S6 (loop, Moufang, nonassoc, Fin50
transport), S7 (classes, 15/1/7 type, non-isomorphism, conjecture
negation). Full plan: results/343790-blueprint.md. verify_frozen after:
356 OK. Credit 0; 52/60 unchanged. No acceptance claimed.
