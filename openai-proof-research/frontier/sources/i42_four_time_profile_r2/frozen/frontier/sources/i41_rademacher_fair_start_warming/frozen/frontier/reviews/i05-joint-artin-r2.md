# Independent review of i05 joint Artin, round 2

2026-10-08. Accepted premises: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and the previously reviewed R006. This is an independent deduction audit, not an upstream-truth audit. No agents, staging, commits, or shared-file edits were used. The associated new investigation is [i06](../iterations/i06-cubic-reservoir.md).

**Proof verdict: PASS for i05 Propositions 1–3 and the Q/F/C algebraic reduction. CR remains unproved. Novelty verdict: none of Propositions 1–3 or the algebraic criterion supplies the requested second substantial theorem.** I found no substantive mathematical correction necessary in those three propositions. The precise attribution and scope qualifications below must be retained.

I read AGENTS.md, the pin, the catalogue's relevant arithmetic/Hecke entries, the iteration record, R006, its full 439-line proof and 255-line audit, all of i05, and the actual source interfaces cited below. The primary Moree–Stevenhagen and Anwar–Pappalardi PDFs were independently downloaded; their hashes agree with i05. The author's entire diagnostic script was copied into this round's assigned directory and reproduced byte for byte.

## 1. Exact primary-literature criterion

Moree–Stevenhagen, *Computing higher rank primitive root densities*, §5, equation (5.2), Theorems 5.6 and 6.2, classifies the Haar-measure obstruction. For a nonempty finite list of rational numbers different from 0 and ±1, absence of an odd square relation is exactly the condition that the map sending every listed squareclass to −1 is well-defined. Once this holds, the remaining obstruction is precisely:

* the squareclass of −3 lies in the kernel of that character; and
* every character of the cubic span kills at least one listed cubic class.

Thus i05's `Q and (not F or C)` is the correct translation. In the printed wording of Theorem 6.2(b), “a character contains an element” means **its kernel contains the element**. The cubic condition is a simultaneous avoidance of hyperplanes, not merely the assertion that none of the individual bases is a cube. The example `(5,−15,600,1029)` is already printed immediately after Theorem 6.2. This is not a new algebraic criterion.

Anwar–Pappalardi, *On simultaneous primitive roots*, main theorem (pp. 35–36), Proposition 1, and Lemmas 1, 4, 5 provide independent confirmation. Their even-product condition `product a_i in −3 Q*²` is exactly F under Q: exponents may be reduced modulo 2, and the character value records the parity of the selected subset. Their existence of a prime `ell=1 mod 3` with all bases noncubic is equivalent to C by Kummer theory and ordinary fixed-field Chebotarev. Lemma 1 supplies the same quadratic-reciprocity/CRT construction used by i05; Lemma 4 combines quadratic and cubic local conditions. Lemma 5 realizes the cubic condition in a progression of **Eisenstein prime elements**, not in a progression of rational primes. Its final infinitude proof assumes Hypothesis H for two norm polynomials. It does not supply CR or a positive-proportion statement.

Moree–Stevenhagen's identification of their algebraic density with a prime density uses GRH. Anwar–Pappalardi's main infinitude theorem uses Hypothesis H. Neither hypothesis is silently assumed here. Failure of Q, or F together with failure of C, gives an actual elementary finite obstruction regardless of those hypotheses. Sources: [Moree–Stevenhagen v2](https://arxiv.org/pdf/1203.4313v2), [Anwar–Pappalardi](https://www.impan.pl/shop/publication/transaction/download/product/92279).

## 2. Proposition 1: universal residual index dividing 2

The proof is correct. In the initial class `11 mod 12`, `v_2(p−1)=1` and `3` does not divide `p−1`. For a fixed cutoff Y exceeding all exceptional degree-drop primes, the union avoiding 1 at every additional odd prime has weight

`w(Y) = (1/phi(12)) product_(5≤q≤Y) (q−2)/(q−1) asymp 1/log Y`.

R006 gives a reservoir of mass `c(theta)w(Y)` in this entire union, with `0<theta<10^−6`. If `p−1=mQ`, `Q>x^(1−theta)`, and Q divides any one of the finitely many indices, then p divides a nonzero factor in `product_(j≤ceil(2x^theta)) |a^j−1|`. Its logarithm is `O_a(x^(2theta))`; this gives `o(N(x))` exceptional primes, also for negative bases. For the other index primes, the all-q splitting bound sums to `(C_A/Y+o(1))N(x)`, with C_A independent of Y. This use is of the field/smoothing lemmas in P §7, not merely its final restricted-q proposition.

Choosing Y after theta and before x closes the budget because `Y w(Y)` tends to infinity. Every surviving odd index prime has been excluded, while the 2-adic valuation of the whole group order is one. The conclusion is **index divides 2**, not merely that the index has no odd prime factors. No independence among the Kummer fields is required. The empty list is immediate. The positive-square example `{4}` proves that universal index one is false.

## 3. Proposition 2 and the realization lemma

The linear extension of the squareclass character includes the sign, 2, and 3. The four units modulo 8 realize the two independent signs of −1 and 2. At an odd support prime ell the required Legendre sign is

`(u/ell)=w(ell) w(−1)^((ell−1)/2)`.

For ell≥5 both possible signs have a representative different from 1. For ell=3 only the negative sign does. Therefore avoidance of 1 modulo 3 is possible exactly when F fails. Lifting a residue 1 modulo 3 to 4 or 7 modulo 9 makes `v_3(p−1)=1` without changing any quadratic signs. The proposed modulus `72 product_(ell≥5, ell|product a_i) ell` is sufficient.

Under Q, nonsquareness excludes 2 from every index; the same reservoir/tail argument excludes all index primes ≥5. The valuation cap at 3 therefore gives **index divides 3**. Conversely an index dividing 3 is odd, so in a cyclic group the exponent of every base relative to a primitive root is odd. An odd square relation makes this impossible at every odd unramified prime. This proves necessity, not merely a density obstruction. In the branch not F, 3 is also excluded from the group order, giving simultaneous index one.

The example `{8,−24}` is valid: its squareclasses are 2 and −6, whose product is −3; 8 is a rational cube. These bases cannot both be primitive in the forced `p=1 mod 3` branch. Signs of negative squares are handled correctly. The parameter choice and eventual lower-bound budgets in i05 are sufficient in every real dyad. These are routine deductions from R006, rather than a new analytic advance.

## 4. Proposition 3: the claimed cubic obstruction

This proposition is correct, including the constant 4/9 and the periodic-classification assertion. The quadratic conditions for `{2,−6}` give exactly `p=13 or 19 mod 24`, outside 2 and 3. Valuations show that the classes of 2 and 3 are independent modulo rational cubes. They remain independent over `E=Q(zeta_3)`: if r is rational and r is a cube over E, taking the norm shows r² is a rational cube, and hence r is a rational cube.

Consequently `Gal(L/E)=F_3²` for `L=E(cuberoot(2),cuberoot(3))`. Complex conjugation acts by negation, so `Gal(L/Q)=F_3² semidirect C_2`. Its commutator subgroup is the entire translation subgroup: `(−2)v` ranges over it. Thus its maximal abelian subextension is exactly E. For **every** fixed M divisible by 24,

`L intersect Q(zeta_M) = E`.

In the fiber above a reduced compatible b modulo M there are nine translations. Rational conjugacy pairs v with −v; it does not distinguish individual nonzero translations. The good set is stable under this pairing and has the four elements `(1,0),(1,1),(2,0),(2,2)`, because the conditions are `s≠0` and `s+t≠0`. Chebotarev therefore gives absolute density `4/(9 phi(M))` and relative density 4/9. The complementary relative density is 5/9.

Refine the period of any Boolean periodic predictor with 24. In every compatible reduced class, a prediction of 0 incurs error 4/9 and a prediction of 1 incurs error 5/9. Their finite weighted sum has error at least 4/9, relative to all simultaneous-nonsquare primes. This also proves the finite-progression impossibility after deletion of a set of zero prime-relative density. The constant function 0 attains the lower bound. No statement here excludes approximation using a modulus that grows with x; i05 only claims fixed periodicity.

This is an obstruction to rational-progression encoding, not to simultaneous primitive roots and not to a theorem obtainable from stronger source interfaces.

## 5. Corrections and qualifications to preserve

No repair to Propositions 1–3 is required. In integrating them, use the following exact wording rather than stronger alternatives:

1. Attribute the Q/F/C criterion and the CRT realization to the primary work above. A source's finite-density obstruction is not an unconditional asymptotic theorem.
2. The special role of 3 concerns a freely chosen global progression. An independently prescribed progression can force other index primes.
3. “Every compatible AP” means each **fixed** reduced class, with finitely many ramified primes discarded. It does not supply an error estimate uniform in a growing modulus.
4. The 4/9 error is relative to simultaneous-nonsquare primes; the absolute density of that ambient set is 1/4.
5. CR cannot be obtained by multiplying Chebotarev and PD marginals. For the required theta, the PD event has mass less than `2·10^−6`, easily small enough to lie wholly in the cubic-bad event of mass 5/9 in an abstract coupling.
6. An unknown positive reservoir constant for each M does not close the tail budget. A common factor, or an explicit dependence satisfying the Y-budget, is required. Positivity only at M=24 is insufficient for the stated proof.
7. The new i06 scalar trace estimate resolves part of i05 §7's fourth attempted route; it does **not** retroactively establish a Frobenius-weighted rough model or the missing extraction. CR must remain labeled unproved.

## 6. Reproduction, independent tests, hashes

Run from the project root:

```bash
python3 frontier/experiments/i06_cubic_reservoir/reproduce_i05.py
python3 frontier/experiments/i06_cubic_reservoir/independent.py
python3 frontier/sources/i06_cubic_reservoir/verify.py
```

The reproduced i05 JSON is byte-identical: all three batches of 2,516 quadratic/CRT tests, 415,888 reciprocity checks, the cubic enumeration, and the reported index tests agree. This certifies reproduction, not the asymptotic proof.

The independent script checks the order-18 group and its order-9 commutator subgroup, the four-trace indicator identity on all nine translations, 4,784 actual split-prime trace identities below 100,000, and 9,568 oriented primary-generator/cubic-symbol checks. It visits all 432 occupied primary unit residue classes modulo 72. The two primes 67 and 139 have the same rational residue 67 modulo 72 and are both 19 modulo 24, but the former is cubic-good and the latter cubic-bad. Their primary generators and cubic labels are recorded. Exact CRT counts are checked for eight unions, and 48 reservoir diagnostics use theta=1/4 or 1/10, not the required tiny theta. All assertions pass.

Important source SHA-256 values:

* Moree–Stevenhagen v2 PDF: `2d65e29feeee744865a49abb4732a18079b54676cd0925bfe35ba8105ea583d7`.
* Anwar–Pappalardi PDF: `2beff9233882d0e01baccec1e0b6f1ec4251802781266b4302b71704a166f6e3`.
* D correlation section: `09d0d46506b82c0cc8c0f04d5c4ff39abe9b6699b7ab04078e73f759d6c46f1d`.
* P splitting section: `b8dc6a9385c2bf695544b5b81e8460dd053083f2346dc6a1d8a81f6dfc084a94`.

Full URLs, pinned Git-blob comparisons, input snapshots, and additional hashes are in [verification.json](../sources/i06_cubic_reservoir/verification.json), [new-source-manifest.json](../sources/i06_cubic_reservoir/new-source-manifest.json), and [literature-manifest.json](../sources/i06_cubic_reservoir/literature-manifest.json).

**Separate verdicts:** the audited deductions pass under the stipulated premises; the novelty/significance gate for a second substantial result is not met. The new analytic work and the exact remaining lemma are in i06. No global priority certification is made.
