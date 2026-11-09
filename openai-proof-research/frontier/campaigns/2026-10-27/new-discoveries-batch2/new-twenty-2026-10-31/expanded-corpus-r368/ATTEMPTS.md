# R368 ordinary attempts and exact source bridges

All deductions below are ordinary mathematics. No mathematical program, enumeration, solver, CAS, numerics, formal API, Lean, or delegate was run. Credit0; no significant qualified candidate.

## 345078 — complete classical-input bridge, including axes and thin strips

Sidokhine Section3 changes its earlier wedge convention: Gamma_G={a+bi:a>0,b>=0}; K_pi consists of Gaussian primes with nonnegative coordinates; odd excludes divisibility by1+i. Conjecture3 asks for uniform constants c0,k0 and max(a,b)>=c0. The strictly interior three-prime endpoint345077 in historical R101 is different and does not itself exclude this record.

Classical input V: every sufficiently large N=1(mod4) is a sum of three rational primes each3(mod4). This is the specified-residue Goldbach–Vinogradov theorem: Laporta2012 introduction p356 explicitly states the Zulauf–Ayoub common-modulus theorem; take modulus4 and three residue classes3. Zulauf Compositio15(1962–1964), pp64–69, introduction formula(2) records the representation asymptotic. Its PDF text layer drops some display equations, so no visual display-verification claim is made. Original1953/1954 analytic proofs are unread. The readable Laporta statement is the precise classical input, not a new analytic proof.

Choose integer T>=1 such that V holds for N>=T. Set B=max(10,T+9). For every integer n>=B choose t in{0,1,2,3} with n-3t=1(mod4). Then n-3t>=T; append t copies of3 to its three-prime representation. Every n>=B is therefore a sum of at most6 rational primes3(mod4).

A rational prime r=3(mod4) is irreducible in Z[i]: a nonunit factorization would force both factors to have norm r, impossible because sums of two squares are never3(mod4). Z[i] is Euclidean, so irreducible implies prime. Its associate ir is prime too. Both are in K_pi and odd. The Gaussian integers2+i and1+2i have prime norm5, so are also odd primes in K_pi.

Put c0=3B and k0=max(12,B+5). Take a>0,b>=0,max(a,b)>=3B.
1. If a,b>=B, represent each coordinate by at most6 rational primes3(mod4), using real and imaginary axis primes respectively. Total<=12.
2. If b<B, then a>=3B. Subtract b copies of2+i, leaving the real integer a-2b>=3B-2(B-1)>B. Represent that by<=6 axis primes. Total<=B+5. This includes b=0.
3. Otherwise a<B and b>=3B. Subtract a copies of1+2i; the remainder i(b-2a) has b-2a>B. Represent it by<=6 imaginary axis primes. Total<=B+5.
These cases exhaust the exact literal source domain. All summands have nonnegative coordinates and are odd Gaussian primes; the constants are uniform.

Why zero: this full construction is coordinate bookkeeping and bounded-strip repair applied to an established fixed-progression additive basis theorem. It introduces no new prime estimate. The exclusion recommendation is based on this explicit complete reduction, not shortness or familiarity. Source-proof qualification remains limited: original analytic proof bodies and all journal/errata companions are not cleared. No new significant candidate or Pi task.

## 340107 — exact partition-function reduction; two failed extensions

Let D_{k-1} be the graph on[1,k-1] joining distinct integers comparable under divisibility. Primitive sets are exactly independent sets. Write Z(G) for the number of independent sets including the empty set, and P_k={d<k:d divides k}. Adjoining k is a bijection between primitive subsets of[k-1] avoiding P_k and primitive subsets of[k] containing k. Thus
 g(k)=Z(D_{k-1}-P_k)/Z(D_{k-1}).
All denominators are positive. For coprime n,m>1 the target is EXACTLY
 Z(D_{nm-1}-P_nm) Z(D_{n-1}) Z(D_{m-1})
 <= Z(D_{nm-1}) Z(D_{n-1}-P_n) Z(D_{m-1}-P_m).
The prime-power target is EXACTLY
 Z(D_{p^(i+1)-1}-P_{p^(i+1)}) Z(D_{p^i-1})
 <= Z(D_{p^i-1}-P_{p^i}) Z(D_{p^(i+1)-1}).
These are full endpoint reductions, not empirical certificates.

Attempt A: P_{p^i} grows, suggesting decreasing avoidance events. But the underlying uniform-independent-set measures have different ambient graphs. New vertices can exclude old divisors and increase avoidance. Event containment under one law does not compare two laws. A monotone coupling is unpaid.

Attempt B: factor proper divisors of nm and invoke negative association or a product injection. General independent-set avoidance has no such negative association: on a three-vertex path a-b-c, Z=5, P(a absent)=P(c absent)=3/5, while P(a,c absent)=2/5>9/25. Also the full interval[nm-1] contains mixed vertices that do not decompose into independent copies of[n-1] and[m-1]. Deleting them changes both partition functions; an injection on divisor sets alone does not establish the displayed inequality.

Exact anchor: for a prime p, P_p={1}, and the only primitive set containing1 is{1}. Therefore g(p)=1-1/Q(p-1). This helper proves neither the mixed coprime inequality nor prime-power monotonicity.

Source McNew Section5 Conjecture1 asks precisely both inequalities and reports checking n<899. Angelo's Theorem1 proves existence of lim Q(n)^(1/n), not these pointwise comparisons. The record's solved reference is misapplied. Missing lemma: a valid comparison/injection for the displayed ambient-changing partition functions, including mixed vertices. No full proof, no new computation, no current literature or formal clearance.

## 339992 — dominance moves and stabilizers; two failed counterexample models

For H<=Sym(X), a coloring of type lambda is a partition of X into labeled blocks of the prescribed sizes. It distinguishes H if its setwise color stabilizer is trivial. H consumes lambda when such a coloring exists. lambda>=c mu quantifies EVERY H consuming lambda. The conjecture identifies this order with dominance when |X| is prime, for arbitrary subgroups, not just transitive groups.

Ji Definitions5.2–5.3, Theorem5.4 with proof, Example5.6 and Conjecture8.7 were read. The established implication is consumption=>dominance. Refining a distinguishing coloring works because the new stabilizer is a subgroup of the old trivial stabilizer. That proves consumption under block splitting for every group, with no primality assumption. Dominance covers can instead move a point between two nonsingleton blocks and need not be refinements.

Attempt A: move x from A to B. A permutation preserving A\{x} and B union{x} can exchange x with an old point of B, so need not preserve A,B. Stabilizer containment fails. The source's regular V4 action on4 points realizes the failure: it consumes(3,1), but every(2,2) coloring has a nonidentity stabilizer. A prime-degree point-moving lemma would be additional mathematics, not an immediate refinement argument.

Attempt B: pad that V4 obstruction with fixed points. At p=5, H consumes(4,1) by isolating an orbit point. It also consumes(3,2): put a fixed point f and an orbit point x into the2-block. A stabilizer must fix x, so is trivial in the regular V4 action. More generally this same singleton-pair rescue defeats the candidate pair(p-1,1)/(p-2,2) whenever fixed points are added. Adding independent V4 orbits increases the number of separating colors required and does not automatically preserve dominance. No witness is claimed.

Attempt C: a regular group of prime degree is C_p. Every nonidentity element is a p-cycle, so no coloring with at least two nonempty blocks is preserved. All nonconstant types are consumed; this model cannot separate the orders.

Precise missing lemma: for every prime p, every H<=S_p and every dominance pair lambda>=mu, existence of a distinguishing lambda-coloring implies existence of a distinguishing mu-coloring. Alternatively one exact H, one distinguishing lambda-coloring and a universal nonexistence proof for mu would refute it. Neither is obtained. The source's p=2,3,5,7 examples are not a universal proof; no finite search or group classification was run.

## 338647 — exact public proof, endpoints included

Albin–Clemens–Fernando–Poggi-Corradini1612.00435v3 Definition6.1, Theorem6.2 and entire proof (lines906–988) were read. Put q=p/(p-1). Their delta_p=Mod_p(paths)^(-q/p)=d_p^q. Blocking duality identifies it with Mod_q(cuts). Every ab cut separates a,c or c,b, so monotonicity and subadditivity give delta_p(a,b)<=delta_p(a,c)+delta_p(c,b). Symmetry follows by reversing paths; distinct endpoints have positive finite modulus; the diagonal is defined as0. Thus d_p^q is a metric.

On P3 adjacent moduli are1 and endpoint modulus2^(1-p), so d_p(endpoints)=2^((p-1)/p). Raising to t requires2^(t(p-1)/p)<=2; hence t<=q. Therefore s(p)=q for1<p<infinity. At p1 the inverse mincut is an ultrametric and all positive powers are metrics: s(1)=infinity. At infinity shortest-path distance and P3 give s(infinity)=1. The exact finite-network endpoint is public, named in the original source's added-in-proof. Zero.

## 340513 — exact public rigidity bridge, not matroid connectedness

Brandt–Speyer1902.05592v2 Corollary3.4 explicitly settles finite-field projective spaces of dimension n>=2. Theorem3.1 and proof and Corollary3.3 were read (lines300–414). The inner Tutte group T0 of PG(n,F) is F* (Dress–Wenzel1990 Theorem3.6). It is finite, so Hom(T0,R)=0. Theorem3.1 embeds the Dressian linearity/lineality quotient into that Hom space. Thus every valuated basis weight is affine on the base polytope and induces a trivial subdivision; Corollary3.3 states absence of matroidal subdivisions. This matches OPS Definition30 indecomposability, not direct-sum connectedness. The public exact theorem defeats discovery credit. Original Dress–Wenzel proof and all nonregular-subdivision foundations were not audited here; no independent foundational proof is claimed.

If raw 'spaces' includes dimension1, PG(1,3)=U2,4 has its octahedron split into square pyramids by x1+x2=1. That is a domain correction, zero, not an eligible new refutation.

## 338298 — public theorem with journal renumbering

Hertling–Mase2108.02295v1 Theorem1.4(a), journal2022 Theorem1.5(a), states exactly the condition(I) conclusion for every standard cyclotomic multiplicity set of an isolated quasihomogeneous singularity. Its proof composes compatibility (preprint6.6/journal6.7) and compatible-set lemma(preprint2.7(b)/journal2.10). The condition definition and lemma proof were read: connectedness and every S_p yield the requested S_2 and T_p. Compatibility ultimately cites2009.08053 Theorem12.1, whose proof is unread here. Public exact statement and connecting proof, zero; no full dependency audit claimed. The earlier paper's examples failing stronger rooted-chain conditions do not refute condition(I).

## 338868 — complete conditional reduction; exact unread-subsumption HOLD

Ho2610.02271v2 Theorem1.1 claims every tree has a bijective prime labeling. Its statement, Section10 assembly proof and Section11 computational-dependency discussion were read. The full324-page dependency chain and frozen supplement DOI10.5281/zenodo.23057222 are unread and unexecuted. Treat this as a specific material possible subsumer, HOLD.

Conditional full reduction: root an arbitrary tree T. At each nonroot v with children choose one child w and the pair(parent(v),w). At the root, if degree>=2, choose any two children. Put all chosen pairs as edges in H on exactly V(T). Each nonroot edge changes original rooted depth by2 and has a unique deepest endpoint: a vertex w can be chosen only by its unique parent. Such edges form a forest, since a deepest vertex of any putative cycle cannot have two edges toward shallower vertices. Each component has a unique minimum-depth vertex. The two root children are distinct minimum-depth vertices in different components, so adding the sole root pair does not create a cycle. Thus H is a forest. Add edges between its components to make a tree on the same n vertices; apply Ho's claimed theorem; delete added edges. The labeling stays prime on H. For each degree>=2 vertex v, the chosen edge is a coprime-labeled pair within its neighborhood; the gcd of all neighborhood labels is therefore1. Leaves impose no condition and bijectivity uses exactly[n]. So all trees, hence lobsters, are neighborhood-prime conditional on the claimed theorem. Asplund–Fox–Hamm Theorem31 proves the gcd step; its Theorem36 already supplies a caterpillar-to-lobster route. If the full subsumer is valid this is a public/source routine bridge, zero; no new candidate.

## Literal/version corrections (all zero)

338773: currentv9 is a Brocard paper with no Goldbach conjecture. Version1 restores Lambda0(n)=log n on primes, zero otherwise, and Conjecture4.1. Its abstract excludes N=2p and discusses even N>6; the record omits these. N10 refutes the unrestricted literal endpoint through positive convolution at5=2+3 and zero convolution at2, but is source-excluded. No source-qualified non-endpoint refutation is claimed. Neither source theorem nor empty solutions establish novelty.

339820: the source uses ~ for CONSECUTIVE avoidance, not ordinary Wilf-equivalence. All length3 patterns are ordinarily Wilf-equivalent (Catalan counts). Consecutive123 versus132 already have different n4 avoidance counts: each start position has4 occurrences in S4; the two events intersect only in1234 for123, and are disjoint for132 (middle inequality contradictions). Thus17 versus16 avoiders. Unequal avoidance precludes strong consecutive equivalence. This is the source's explicit ordinary/consecutive warning and an ineligible literal correction; intended Nakamura converse remains unresolved here.

339144: source fixes n>=2, record permits positive n. At n1 every power permutation preserves its single class. For every prime p>3, f(x)=2x is a permutation, distinct from both +-x, giving infinitely many literal Type(i) and(iia) examples. Source-excluded endpoint, zero. For n>=2, fixed-n finiteness from Theorem1.2 is weaker than the source's global p>2n Conjecture2.2. PartII companion unread, HOLD.
