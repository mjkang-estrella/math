# BBK full refinement: corrected handoff

2026-10-29 UTC. Root inspected the completed Pi lane `pi-bbk-full-refinement-r3`, the actual primary Section 5 (fresh public HTML read), its identity script and its k=6 reconnaissance. **No acceptance. Credit 0.** The k=4 and k=5 certificate claims remain partial and have not received a complete independent certificate audit. Their prose has errors that must not propagate.

## Literal target and exact all-order identities

Banerjee–Bringmann–Keith, arXiv:2601.04014v1, Conjecture 5.1:

`G(k,n) = (q^(2k-1);q^2)_n / (q;q^2)_(n+1)` has nonnegative coefficients for all integers k>=1,n>=0.

Write `O_m = product_(j=0..m-1) (1-q^(2j+1))`. For k>=2,

`G(k,n) = O_(k+n-1)/(O_(k-1) O_(n+1)) = G(n+2,k-2)`.

This follows by exact product cancellation, not finite data. The equivalent canonical form is

`G(k,n) = (q^(2n+3);q^2)_(k-2)/(q;q^2)_(k-1)`.

The original source Lemma 5.3 is `G(n+2-j,n)=G(n+2,n-j)`, 1<=j<=n. Its statement agrees with the corrected symmetry. Consequently k<=5 rows transfer to **n<=3**, not n<=4. Conditional on the row proofs, the uncovered region is k>=6 AND n>=4.

## Errors caught by root

1. The report's `G(k,n)=G(n+1,k-1)` is false. At (k,n)=(4,0), the coefficient of q is one on the left and zero on the claimed right. `checks/run1_identities.py` actually tests the **correct** symmetry; the dormant `gkn_core.check_reduction` retains the wrong one. Do not adopt either prose or unused checks blindly.
2. G(2,n)=1/(1-q). The report's two-denominator formula belongs to **G(3,n)**, not G(2,n). G(3,n) positivity follows from monotonicity of the denumerant for {1,3}.
3. `run9_k6_probe.py` has four numerator factors but **six** denominator factors {1,3,5,7,9,11}. It probes `G(6,n)/(1-q^11)`, not G(6,n). At n=0 its q^11 coefficient is two instead of one. Its positive reconnaissance is NOT evidence for the literal k=6 assertion.
4. Literal k=6 has denominator {1,3,5,7,9}, period lcm=**315**, denumerant degree **4**, and a 15-point total-degree staircase, not period3465/degree5/21 points. The wrong compute estimate cannot justify the claim that computation is the only obstacle. Even valid finite-k certificates would not prove all k.
5. PROOF-K4-K5 Lemma2.1(ii) uses four-part h but drops the 7-variable in its proof. At x=0, h4(15)-h4(0)=18, whereas sum_(v=1..15)r_(3,5)(v)=12. It is valid after changing h to h135. Proposition2.2's direct separate derivation does not need the erroneous four-part reading.
6. Several cancellation indices and the first notation in Lemma1.2(b) are malformed. The final canonical fractions and explicit eight-term sum are the relevant objects, which the root scope check confirms independently on finite prefixes. This is not a complete validation of every residue certificate.

`check_scope.py` is independent of Pi's implementation. It checks 121 exact identity pairs through degree250 and gives the exact falsifiers above. The mathematical identities are additionally proved by cancellation. No Lean proof exists: the worker's scaffold contains explicit sorrys and is not a certificate.

## Remaining full question; avoid duplicate work

Read `root-bbk-r1/discovery.md` for proved failures of divisibility matching, the weighted-complete-intersection route, odd-cyclotomic prefix positivity, and termwise q-Chu–Vandermonde positivity. None is a counterexample to the full G. The earlier first-campaign `pi-discrete-discovery-r7/FINDINGS.md` also has simple-pole/eventual-periodicity structure and unresolved tail/initial-segment positivity. Chern–Wang2601.19845 proves the motivating summed F positivity, not automatically this G refinement.

The full stronger source Conjecture5.2 is equivalent, in its stated range, to nonnegativity of

`q^(2n+1) (1-q^(2(k-n-1))) (q^(2k+1);q^2)_(n-1)/(q;q^2)_(n+1)`.

Root's prior exact finite scan of this residual is already documented; do not repeat it as a result. No uniform positive decomposition, injection or all-k certificate has been found.

Potential literature directions, **not established bridges**: Corteel–Savage *Lecture Hall Theorems, q-series and Truncated Objects*, arXiv:math/0309108, especially odd/even refinements; Gatzweiler–Krattenthaler *A positivity conjecture for a quotient of q-binomial coefficients*, arXiv:2502.06032v3 (same-top polynomial quotients are a different scope; the general positivity there is itself conjectural). Their theorem bodies still need a careful applicability check. Root's PMC attempt for the latter met a browser challenge and stopped; arXiv is a lawful separate primary copy. No subsumption claim is made.

## Next investment rule

Seek the FULL source question. Do not spend another round just enlarging the fixed-k table, rebuilding partial Lean scaffolds, or certifying a wrong-object smoothing. Recheck the CURRENT public registries and source followups before investing. Any numerical evidence must remain labeled as such. Root has not issued a fresh worldwide-novelty clearance. Preserve the Pi lane unchanged and record any repairs in a separate lane.

Primary source read: https://arxiv.org/html/2601.04014v1, equations5.1–5.2 and Lemma5.3. Counts remain3additional/33total. The two infinite-row claims are neither accepted nor counted.
