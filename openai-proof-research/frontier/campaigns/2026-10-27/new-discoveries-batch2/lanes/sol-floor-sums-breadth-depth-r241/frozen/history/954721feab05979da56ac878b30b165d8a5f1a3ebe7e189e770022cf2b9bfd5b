# Research disposition: full circular-fence identity unresolved, credit 0

No full proof/refutation, PROOF.md, Lean claim or acceptance nomination. Counts remain 3/30 additional and 33/60 total. Finite cases and the algorithmic recurrence below earn no credit.

## Exact selected primary scope

Yakob Kahane, *Combinatorial interpretation of the coefficients of the order polynomial of fence posets*, arXiv:2607.11225v1, 13 July 2026, Definition 4.6, Lemma 4.7, Conjecture 4.8. The live abstract checked 29 October 2026 lists only v1.

For EVERY circular fence poset P with n elements, the conjectured polynomial identity is

    n! Omega(P;t) = sum_{sigma:P bijective->[n]} t^(hat_bl_P(sigma)).

Omega(P;m) counts weak order-preserving maps to [m], for every nonnegative integer m. Thus the conjecture is an all-parameter polynomial identity, not an asymptotic assertion or a fixed-crown problem. Circular fence means that the undirected Hasse diagram is a cycle. Represent vertices by i modulo n, and let a_i=1 when i-1 <_P i, and a_i=0 for the opposite relation. Both orientations must occur at least twice; one occurrence makes one proposed cycle edge transitive rather than a Hasse edge.

A proper connected block is a convex cyclic interval, rooted at its first vertex. For every other vertex y in that interval, sigma(y)<sigma(root) for a_y=1 and sigma(y)>sigma(root) for a_y=0. The whole cycle is a block when some root x satisfies a_y=0 iff sigma(y)>sigma(x) for all y. Between distinct blocks, every poset comparison must point in the same direction as the comparison of root labels. Lemma 4.7 asserts a unique valid partition; hat_bl counts its blocks. Source defects or uniqueness failures would need separate diagnosis, not automatic relabeling as an identity counterexample.

## Early source and prior-proof screen

The ancestor/campaign rules, NEXT, ledger, prior context, and fresh discrete/finite/arithmetic/algebra/matrix-geometry lane summaries were read before choosing this target. No named excluded family was developed. Reused the explicitly authorized current registry evidence, with verified hashes: Omega head 5517865965160e8d20e4122aafe4e6c468c6c41d checked about 06:53 UTC; complete D5 and Problems trees fetched 06:54 UTC, 12,445 and 1,538 entries, truncated=false. The count registry and OpenAI complete preprint subtree/catalogue are dated 04:39–04:43 UTC, with heads rechecked equal in that review. These are DATED path/title screens, not current full-text clearance. No repeated API traversal was made.

Initial distinct lead: Bóna–Maga–Richey 2606.06655v1 Conjecture 3.1, for equal-length binary v,w outside {1^(k-1)0,10^(k-1),0^(k-1)1,01^(k-1)}, |v|_1<|w|_1 implies rho^v>rho^w and q^v<q^w. Actual v2 Section 3.1 explicitly says that original conjecture is false and acknowledges three readers' size-four counterexample. STOPPED; no new witness/proof claim. Its different Conjecture 6.1 rho-half clause has a public Omega proof dossier; also excluded. Search results likewise showed public resolutions of Almkvist unimodality, Brenti log-concavity and chromatic e-log-concavity; no independent theorem-body validation of those discarded search leads is claimed.

Closest bodies read for the selected target:

* Kahane Theorem 3.8 proves the linear fence identity; Section 4.2 still labels the circular identity a conjecture. Sections 3 and 7 give linear-fence block and coefficient recurrences.
* White 2609.17561v1 Theorem 1.2 states the full two-row rectangle version of the DIFFERENT skew-shape Conjecture 4.4. No credit for any rectangle instance. White Section 1.1 says Kahane proves the identity for circular fences, whereas Kahane's actual current text says Conjecture 4.8. This bibliographic discrepancy remains unresolved; White's statement is not evidence of a circular proof body. The paper's full two-row proof has not been audited here.
* Ferroni–Morales–Panova 2503.16403v1 Theorems 1.1/4.2 prove skew-shape order-polynomial coefficient nonnegativity. Proposition 7.5 proves nonnegativity for alternating closed zig-zags and gives linear coefficient 1/binom(2r,r). These statements do not identify Kahane's statistic on every circular orientation. No credit for positivity or this known coefficient.
* Shareshian–Wright–Zhao math/0311426, Theorems 2.6/2.7 and Proposition 2.9: general ideal-convolution and finite-difference formulas for labeled order polynomials, with linear-coefficient expansion. These do not by themselves identify the circular statistic. An all-parameter bridge would still need proof and substantive assessment.

Live searches on title, arXiv ID, author/circular-fence/conjecture terms did not yield a body settling Conjecture 4.8. This does not establish novelty. The registry screen had no Kahane/fence path match. No MathDB live solution-array clearance was attempted or inferred. No published-version body beyond these actual preprints was located/read.

## Mathematical route and exact gap

Let C_a(t) be the normalized generating polynomial of the following finite algorithm on all n! distinct labelings. Repeatedly take the largest remaining label at vertex i. If a_i=0, delete that vertex and its incoming edge, retaining the outgoing sign at its successor; block count is unchanged. Once the largest remaining label is an ascent, cut immediately before it. Scan the resulting linear list, keeping the current root label r. Start a new block at y exactly when (sigma(y)>r) equals a_y, then replace r by sigma(y). This implements the construction in Lemmas 4.7/3.3 on tested inputs.

For this ALGORITHMIC polynomial, conditioning on the location of the maximum proves the exact recurrence

    n C_a(t) = sum_{i:a_i=0} C_(a with i deleted)(t)
                 + t sum_{i:a_i=1} F_(Q_i)(t).

Here Q_i is the linear interval from the first descent strictly after i around the cycle through the vertex just before i. If there is no descent, Q_i is empty. F is the normalized linear greedy-block polynomial; by source Theorem 3.8 this equals the weak order polynomial of the corresponding fence.

Proof for the algorithm: the maximum position has probability 1/n, and deleting a descending maximum leaves every relative order uniformly distributed on n-1 labels. At an ascending maximum, the maximum is a new root and absorbs every ensuing ascent until the first descent. That descent necessarily starts a new root, and the rest is the ordinary greedy path algorithm on Q_i. The relative labeling on Q_i is uniform, independently of labels removed from the initial run. If every edge is ascending, there is one block, so C_a=t. These cases exhaust the finite algorithm. This is only a helper mechanism, not the source result.

Two precise obligations remain:

1. Prove uniform equivalence of this algorithm with the literal valid convex-block statistic, including every contracted orientation. A descent contraction can leave the Hasse-cycle domain: starting with the alternating four-cycle (1,0,1,0), deleting one descent leaves a triangle with a redundant edge. Source Conjecture 4.8 cannot be invoked inductively on that triangle. The intermediate algorithm remains defined, but the source bridge has not been supplied uniformly.
2. Establish the SAME recurrence for Omega of all the cyclic inequality systems needed by those contractions, or a different exact identity proving C_a=Omega(P;t) for every genuine Hasse cycle. This is the central all-order missing mechanism.

An independent exact representation of Omega(P;m) is trace(T_0 ... T_(n-1)), where (T_i)_(x,y)=1[x<=y] for an ascent and 1[x>=y] for a descent, with cyclic indices x,y in [m]. This follows by expanding the trace: its summands are exactly all cyclic assignments satisfying every cover inequality. A uniform trace/path identity matching the preceding algorithmic recurrence would be a concrete route; it is NOT proved by the finite evaluations.

Naively cutting one edge and applying the proved fence theorem loses a constraint. For the alternating four-cycle K_2,2 there are 7 weak maps to [2], whereas cutting any one cover gives 8. Thus one cannot simply identify the path and cycle order polynomials. This is a method obstruction, NOT a source counterexample.

## Exact validation and limitations

Run, from this lane, `python3 check.py`, `python3 independent_check.py`, and `python3 recurrence_check.py`. Each executable enforces a hard 512 MiB address-space cap, a 30- or 45-second CPU cap, and BLAS/OMP thread limits of 1 before work.

check.py enumerates 88,368 labelings of 32 rotation-representative genuine cycle orientations on 4..7 vertices. Every histogram agrees with the independent weak-map transfer evaluation at m=0..n. Those evaluations suffice to certify each TESTED polynomial, since both have degree at most n, but say nothing about untested n.

independent_check.py imports no code from the first checker. It enumerates every convex cyclic-interval partition and tests the literal root inequalities and all transitive block comparisons. On 7,728 labelings of 16 orientations through six vertices, exactly one valid partition is found and its histogram matches the first checker. It separately brute-forces all maps to [2] and [3] (32 tests).

recurrence_check.py implements a third recurrence computation and compares it with the first histograms at 232 evaluations. It also verifies the 7-versus-8 cut obstruction. All completed normally. These are independent implementations by the same solo worker, not independent adversarial review by another agent. No numerical approximate arithmetic is used.

Strongest falsifier: one genuine Hasse-cycle orientation with an exact coefficient or integer-evaluation mismatch between the literal valid-block histogram and n! Omega; alternatively a failure of the uniform algorithm/source bridge. No such witness was found in the bounded tests. Lack of a witness is not a proof. No Lean investment is justified before a complete ordinary argument and eligibility clearance.
