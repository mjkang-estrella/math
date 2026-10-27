# Norm-compression screen — no discovery, credit0

MathDB406427 asks the lower branch of the general 2-by-N Schatten norm
compression inequality: ||T||_p >= ||[||T_ij||_p]||_p for 1<=p<=2.
This is Audenaert2008 Conjecture1, primary arXiv:math/0702186v2 p2,
LAA428(2008)781–795 DOI10.1016/j.laa.2007.08.007. The upper branch reverses
for p>=2; the source proves lower-branch sufficiency for the dual upper branch.
Known special cases include compression rank1, all blocks rank1, proportional
blocks within each row, p>=4, and some two-column cases. They are uncredited.

The MathDB-associated 2610.11021v2 (Vuong–Osaka) proves a DIFFERENT
Lin–van den Driessche assertion: for a positive 3-by-3 block matrix H,
[tr|H_ij|^p] is positive semidefinite (Theorem1.2/Corollary3.1).
This does not by itself prove/refute the general 2-by-N compression conjecture.
Actual source statements were read in the downloaded PDF text. No rendered-page
or whole-proof reading is claimed for this screen, and no acceptance gate is
claimed. The local public registry also explicitly leaves the general
2<p<4 upper branch open; its reduction is not a full proof.

search.py uses complex 2-by-2 blocks in a 2-by-3 arrangement, jointly normalized
at every evaluation. Analytic SVD gradients were checked against central finite
differences (max discrepancy 5.088109517e-10). For each p in
{1.1,1.5,1.9,2.1,2.5,3,3.9}, 24 BFGS starts with max600 iterations were run.
Every apparent violation ratio was within 2.5e-15 of1, i.e. roundoff.
No counterexample, no proof, no claim about unsearched dimensions or exponents.
Full numerical result and script are retained. No Lean/manuscript investment
or new ledger exclusion is justified; the general problem remains unresolved
by this work. This is finite computational evidence and a source distinction,
not a new mathematical discovery.
