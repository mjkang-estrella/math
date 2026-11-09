# Ordinary proof attempts and exact gaps

Research only, 2026-11-05. No new theorem or counterexample is claimed. No Lean, solver, numerical sweep, child agent, git action, shared-file edit or external message was used. These are sustained symbolic routes, not completed certificate plans. Root should not start Pi execution from this report.

## 320285 / 322077: one universal-word family

Read Denton 1008.2401, Corollary 3.3, Proposition 3.4, branching section and §6.1; compared thesis 1108.4379 §2.6 (Conjecture 2.6.1). The literal targets coincide. Mask a positive letter by pi_i and a negative one by 1-pi_i, in the complex 0-Hecke algebra. Demipotent means that some positive power is idempotent; having spectrum contained in {0,1} is insufficient.

First route: order the permutation basis by weak order and use triangularity. Each generator pi_i fixes a basis vector or moves it strictly in weak order; 1-pi_i has the corresponding triangular action. The product therefore has diagonal entries 0 or 1. Because every index occurs, a diagonal entry is 1 exactly for a basis permutation whose descent set is the positive set of D. This is the same elementary triangular mechanism used by the source. It proves that the minimal polynomial divides x^a(x-1)^b for some a,b. It does NOT prove b=1. A 2 by 2 unipotent Jordan block gives a precise obstruction to the shortcut. Its powers never stabilize in characteristic zero.

Second route: use the palindrome u_N = (1,u_{N-1} shifted by one,1) to induct on N. Writing e for pi_1 or 1-pi_1 and V for the inner signed product gives U=eVe. Even if V is demipotent, compression by a noncommuting idempotent need not preserve demipotence. The source's diagram-demipotent branching proof uses sibling rivalry; §6.1 explicitly says these words fail that property. No substitute identity eV^m e = (eVe)^m, nor a bound annihilating the 1-primary nilpotent part, was obtained. The source already checks N<=9, so recycling those finite cases cannot solve the conjecture.

Third route: descend to nondecreasing parking functions. The source explicitly proves idempotence of the masked word in that quotient, but the additional relation pi_i pi_{i+1} pi_i = pi_i pi_{i+1} destroys information. An element in the kernel can still create a nonzero Jordan block at 1. Quotient idempotence alone is not a lift. No kernel-annihilation lemma was found.

Exact remaining mathematical lemma: for every N and D, the 1-primary component of left multiplication by U has zero nilpotent part. Equivalently, with d=N!, U^d(U-1)=0 (given the established 0/1 spectrum in the faithful regular representation). A nonzero value would refute demipotence, but no such value or size is known. This criterion is an algebraic reduction, not a justified finite search assignment. Naive N! storage exceeds a sensible small certificate budget already at the first unchecked N=10. Literature/version and journal qualification are incomplete; no novelty clearance.

## 319817: binary code dimensions from conic flags

Read Couvreur 1004.3774 v3, definitions of C_1,C_2, Propositions 5.6–5.7 (explicit parabola/hyperbola equations), §6–§7 flag-incidence setup at the definition level, Definition 8.1, Theorem 8.2, and §8.3 Conjecture 1 / Lemma 8.8. Compared v2 conjecture and v1 opening/setup. The codes are over F_2 even when the geometry is over odd F_q. They are kernels, not row spaces, of incidence matrices. Lengths are n_1=q^3 and n_2=q^2(q-1); a matrix has q^3 rows including exceptional-divisor constraints. Source convention is q>=4, so q=3 is not an eligible shortcut.

The desired ranks, obtained by subtracting the conjectured nullities, are
r_1=(q^3+2q^2-3q+2)/2 and r_2=(q^3+3q^2-9q+7)/2.
This conversion is exact but is not a proof of either rank.

First route: use the q^2 exceptional rows, whose supports partition the flags, to eliminate one direction coordinate at each affine point. This yields q^2 independent parity constraints and a smaller residual conic incidence matrix. The all-ones row is their sum, not an additional independent equation. Counting rows or using the even-weight lemma therefore cannot reach the conjectured residual rank. The source already discusses this redundancy.

Second route: exploit affine translations. The translation group F_q^2 has odd order, so its representations over an algebraic closure of F_2 are semisimple; Fourier projectors divide by q^2, which is invertible. Translation preserves tangency and the conic families. Thus a block decomposition by additive characters is plausible and avoids pretending that real or F_q rank equals binary rank. But the actual character blocks still require evaluation of characteristic-two sums of conic tangent incidences. Neither their exact ranks, their exceptional characters nor a uniform descent back to F_2 was established in this session. Semisimplicity itself does not determine these ranks.

Third route: a finite refutation would need an odd prime power q>=5 outside the source tables (all checked q<=31 pass) and an exact rank certificate for H(i,q). A kernel-independent family plus a row-space upper certificate must prove a discrepancy, rather than merely reproduce an elimination answer. No q, rank defect or witness has been found; a blind q=37 elimination would be execution without a discovered mechanism, not an earned Pi handoff. The q=3 domain omission and source Lemma 8.8 about C(3,q) are excluded: C(3,q) is not the target.

Exact remaining lemma: compute the ranks of every additive-character block of the literal flag-incidence matrix, uniformly in all odd q>=5, or produce one source-eligible block with an exact discrepancy. The journal version and citing-primary proof literature have not been cleared. No complete proof or finite candidate.

## 318450: three-coloured tournament without a cyclic rainbow triangle

Read Georgakopoulos–Spruessel 0904.1967 v2 introduction, Conjecture 1.2, Theorem 1.1, Lemma 2.1 proof and §3 opening; compared v1 target passages. The source proves the locally two-coloured case, not all three-coloured tournaments. The arbitrary-colour bounded dominating SET problem is also different from this one-vertex conclusion. Reversing all arcs converts sink to source convention without changing the conjecture.

First route: Gallai partition induction. The prohibition here excludes only cyclic rainbow triangles. A transitive triangle with its three edges differently coloured is permitted, so a decomposition theorem requiring no rainbow triangle at all has an unpaid hypothesis. The three-vertex transitive example demonstrates that implication is false. This cannot be fixed by silently forbidding the transitive case.

Second route: follow the source's minimal-counterexample reduction. In a minimal counterexample there is a Hamilton cycle C with each vertex reaching every other vertex monochromatically except its predecessor on C. The source also shows that every vertex of a minimal counterexample meets all three colours. Thus the entire locally-two-coloured case is already paid for and cannot yield credit. Deleting one vertex does not preserve the required reachability: the path certifying domination may use the deleted vertex. No induction converting these facts into a contradiction in the all-three-colour case was found.

Third route: a finite refutation could be encoded by one orientation and one of three colours per pair, no cyclic rainbow triangle, and one unreachable vertex for each putative universal source. A certificate needs the actual tournament, for each source v a vertex w and three colour-specific forward-closed sets containing v and excluding w. Such sets prove no monochromatic path without trusting a solver. The source's minimal-counterexample Hamilton reduction could reduce the encoding, but it supplies no upper bound on the order of a counterexample. There is no concrete tournament or justified order budget. A generic SAT formulation alone is not a candidate and is not sent to Pi.

Exact gap: contradiction for the unrestricted all-three-colour minimal counterexample, or an explicit finite tournament satisfying the closed-set certificates. Current literature search located special-case results but did not clear all citing bodies or a current full resolution.

## Compact mechanisms for the remaining IDs

320903: source Conjecture 2 is stronger (no coprime-endpoint restriction), proved there for k=3,4. Lemma 5 covers intervals by good sets but no uniform cover for all k was derived. The record title, actual inequality, and its 'refuted' references disagree. A refutation of the original Erdos extremal conjecture does not automatically refute this auxiliary restricted-endpoint inequality. Do not label this known-refuted from metadata.

320951: the record's definition says kappa(G-X)=k-3 even for X empty, making its literal class empty. The intended source definition uses k-|X|. Vacuity is a domain/wording correction, zero credit. For the intended Conjecture 3.10, the source's 2k^2-k order bound does not imply c k^(3/2) for a fixed c. A finite example cannot refute an existential uniform constant.

323149: adding universal vertices is explicitly excluded by r-primitivity; the source's Cayley families let r grow, so they do not refute finiteness for a fixed r. One would need a fixed-r unbounded-order family with uniqueness for every missing edge, or an order bound. No such mechanism survived.

376081: source Theorem 1.1 and Corollary 1.2 already state exactly the growth endpoint under A–B. Iterating doubling and absorbing its constant is the printed reduction, not a discovery. No independent audit of all analytic proof steps is claimed.

320611: if two equal n-blocks start d positions apart, d<(c-1)n gives a factor of period d and exponent at least 1+n/d>c/(c-1). A Dejean threshold word excludes this. Conversely a repetition above threshold yields such blocks. Thus the literal gap statement is the known Dejean theorem, not an unrelated new strengthening. Primary proof 0905.1129 v3 was read for its threshold definition and all-alphabet reduction; its finite morphism verification was not rerun. The AMS request returned HTML despite HTTP 200 and is not journal-body evidence.

318112: fixed graph or edge-connectivity>=5 lower bounds do not give a universal constant over arbitrary metrized graphs; edge lengths and graph order vary. No reduction paying for low-connectivity pieces was proved. Park.

318731: 2105.01104 Theorem 1.2(b) states for each c>=13, every q,d, at least q vertices have degree>=d; source also explicitly allows simple 2-connected realizations by subdivision. Set c=13,q=14,d=D+1 to refute the reserved bound for every D. This is a direct published theorem application, zero credit. The computer-free base crossing proof was inspected at its final argument; its entire drawing casework was not independently checked. Publisher direct HTTP was 403 and was not retried/bypassed.

318891: near-3^k obstruction proves only the lower bound I(k). It supplies no uniform upper bound. Every finite parameter check or known small exponent is insufficient for the all-k statement. Park promptly.

319313: Gruslys JoCG 2014 Theorem 3 explicitly gives arbitrarily large three-coloured point sets with no four collinear and no monochromatic line. The proof uses a nodal cubic and equal-third arcs of a cyclic subgroup. k=3,ell=4 refutes the literal MathDB assertion. Actual journal proof read through its final modular/interval contradiction. Zero credit.

319362: source Conjecture 1.3 remains distinct from Theorem 1.4's coprime-size/rank case. Copying bases or parallel extending changes the requirement that each original element occur once. No way to remove the gcd restriction was obtained. The source acknowledges an earlier optimistic proof failure; do not promote that withdrawn claim. Current rank-three progress seen as routing only, not read/used as a theorem.

368347: maximal cut proves the finite case; compactness works locally finitely but infinite-degree vertex inequalities are not closed finite constraints. Three-choosability in the cited paper is not two-colourability. Borel counterexamples are not ordinary countable counterexamples. No full route.

317333: minimal-obstruction descent gives that a non-RAAG finite graph contains an obstruction. The other implication requires upward persistence of non-RAAG under graph containment, not minimality alone. Graph braid subgroup embeddings do not suffice because RAAGs have non-RAAG subgroups. Low-index classification beyond the source's n>=5 is unpaid. Literal 'every graph contained in it' must mean proper; exploiting its omitted word is excluded.

317659: Kirsch–Sibley–Sprangel 2209.14198 §4.1 already gives the n=3 obstruction: four isomorphism classes force four vertices, and two three-subsets of a four-set share an edge, preventing both K3 and the independent triple. This is printed correction/prior refutation, zero credit. Their n>=4 corrected conjecture is outside this reservation's literal resolution credit.

317851: Cavenagh–Wanless DAM158 (2010) Theorem 3 proves all k>=3 and s divisible by k with s>=k^2. Substitute s=km. Read Lemma 6's actual transversal construction and final even-even product proof. Their new primary-bitrade conjecture is a stronger different target, not assigned here. Zero credit.

318027: the source's regular triangle-free construction handles k=3; best-known lower bounds or fixed finite Ramsey graphs do not compare to the unknown actual R(k,l) for all l. Adding clone vertices regularizes some constructions but can increase independent sets. No uniform constant-factor regularization theorem was derived.

316272: truncating an entire constant-spectrum curve at degree n does not preserve determinant/characteristic polynomial: coefficients of degrees above n can enforce essential cancellations. Exponential conjugation realizes commutator directions but is generally non-polynomial. No all-matrix polynomial replacement or explicit bounded-degree obstruction was found. Park; primary target passages only, not a completed analytic literature audit.
