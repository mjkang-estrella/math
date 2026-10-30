# r45: fresh full target unresolved; credit 0

No nomination, complete source proof, or source refutation is claimed. Campaign counts remain 5 additional / 35 total. Root alone decides acceptance. Solo; all writes confined to r45.

## Bounded early screen

Two primary papers screened (below the four-primary limit). Reading the second paper's Conjecture 9 and 10 is one related classification target, not an attempt to obtain separate family credit.

1. Leonid Fel, *Symmetric polynomials associated with numerical semigroups*, Discrete Math. Lett. 5 (2021), 56–62, DOI 10.47443/dml.2020.0066. Actual published pp59–62, equations (10), (14), (16), (23)–(26), Conjectures 2.1 and 3.1 read. EXCLUDE: Amdeberhan–Fel–Ono, arXiv:2507.12352v1, Theorems 1.5 and 1.7 explicitly settle these same claims, with complete proof bodies in Sections 3.2 and 3.4. Their power-sum involution fixes p1 and negates even power sums (higher odd power sums are absent). Their tangent-number form is the eliminated version of Fel's binomial recurrence. Multiplying by the powers of T1 recovers polynomial identities wherever normalized fractions make sense; centered parity gives the unnormalized version directly. No new theorem from formalization or zero-denominator repair. Source published March22,2021; successor submitted July16,2025, predating this lane. 24 small exact centered-parity checks merely corroborate the already public result.

2. Xuejun Guo–Zhengyu Tao, *Counterexamples to Stanley's conjecture on dimer coverings*, arXiv:2605.28195v1, submitted May27,2026. Actual entire six-page PDF and matching current HTML obtained. Source Eq(1)–(3), Lemma3, Theorems4/6, Conjectures9/10 and Pell discussion read. SELECT Conjecture10 in full, rather than the already disproved Stanley conjecture. Current arXiv record lists only v1 and no journal reference. No published counterpart located in bounded title searches; journal/followup coverage remains limited.

## Exact selected statement

For every integer k>=1 let ell=floor(k/2),

c_j=cos(j*pi/(k+1))+sqrt(1+cos(j*pi/(k+1))^2),
bar_c_j=-1/c_j,
a_S=product_{j in S}c_j product_{j notin S}bar_c_j.

The *explicit*, generally unreduced Stanley denominator is
Q_k(X)=product_S(1-a_S X) for even k, and
Q_k(X)=product_S(1-a_S^2 X^2) for odd k.

Conjecture10: Q_k has a repeated complex root iff k=14h-1 or k=30h-1 for some integer h>=1. No replacement by the reduced generating-function denominator is allowed: that denominator always has simple roots, as Stanley already observed. Source Theorem4 proves the entire 'if' direction, so reproducing it earns no credit. The missing all-k 'only if' direction is the target here.

Lemma3 equivalently asks whether distinct subsets S,T have product c_S=product c_T; when k is even one must also have |S|=|T| mod2. Conjecture9 proposes classification of indecomposable identities by the four displayed identities at conductors7/30. A proof of that stronger claim would imply Conjecture10, but is absent here.

## Antecedent and public-body comparison

Stanley, *On dimer coverings of rectangles of fixed width*, Discrete Appl. Math.12 (1985),81–87, actual author-hosted published PDF read: explicit root/product definitions and final p87 conjecture, simple reduced-denominator observation, Lagarias odd-prime-except7 irreducibility. Guo–Tao Theorem6 reproduces that known prime case using square classes and Pell numbers; it is not a fresh result.

Live Omega dev13540e54dcb7e367c6799640ec15b707fcf2bb18 at retrieval; 30-commit/61-file compare against r44, with fresh complete untruncated D5 (12552 entries) and Problems (1551). Four other registry heads unchanged; complete hashed r44 scopes reused. These are named subtree scopes, never whole-dev coverage. Matching pathname bodies actually read: Butera dimer virial claim is about finite differences of matching numbers on regular biconnected graphs, not rectangle-denominator multiplicative units. NegativePellSquare's theorem is an explicit norm-minus-one unit identity, not a classification of Sylvester-Pell square values or trigonometric-unit relations. No matching settlement located in this bounded investigation; absent matches provide no novelty clearance. Full global literature, semantic registry coverage and journal comparison remain open.

## Concrete route and its exact obstruction

Write n=k+1 and K=Q(cos(pi/n)). Put a_j=2cos(j*pi/n) in K and
D_j=4+a_j^2=6+2cos(2*pi*j/n), so c_j=(a_j+sqrt(D_j))/2>1.
Let L=K(sqrt(D_1),...,sqrt(D_ell)).

A sufficient classical criterion for multiplicative independence of the c_j is independence of all D_j in K*/K*^2. Indeed multiquadratic sign automorphisms can then flip just sqrt(D_j), fixing K and the other radicals. Such a flip sends c_j to -1/c_j. Applied to any integer multiplicative relation, division by the original relation gives (-c_j^(-2))^e_j=1. Absolute values and c_j>1 force e_j=0 for each j. This is the mechanism behind the source prime case, not a new discovery.

More generally, if e_j in {-1,0,1} gives a subset-product identity, every available sign automorphism v gives e dot v even: the quotient above must be positive. By multiquadratic duality, product D_j^(e_j mod2) must therefore be square in K. This is only a necessary condition, not a converse. Even when radicals are independent over a smaller real field, enlarging to K can destroy independence; the base-field distinction is essential.

The naive all-composite extension fails already at n=15, an input outside the conjectured exceptional denominators. Here K=Q(t), t=2cos(2*pi/15), with
f(t)=t^4-t^3-4t^2+4t+1=0.
The field equality with Q(cos(pi/15)) follows since 15 is odd (or cos(pi/15)=-cos(14*pi/15)).

At j=5, D_5=5 and
(1+2t^3-6t)^2=5 modulo f.
Thus D_5 is already square in K. Geometrically 1+2t^3-6t=1+4cos(2*pi/5)=sqrt5. The proposed independent-radical mechanism cannot even handle this ordinary nonexceptional conductor. This says nothing against the actual c_j independence or simple-root prediction at k=14: a unit already in K cannot be isolated by automorphisms fixing K.

The source's pairwise-coprime-ideal shortcut also fails at n=15. We have norm_K/Q(D_1)=f(-6)=1345=5*269 and D_5=5. Modulo5, f(T)=(T+1)^4; the map Z[t] -> F5 taking t to -1 annihilates both D_1=t+6 and D_5. Equivalently a maximal ideal above this residue ideal in the integral closure contains both radicands (lying-over). This proves overlap without treating differing norms as coprimality evidence. It does not prove any subset-product identity.

A second generic false shortcut is 'square norm implies square element'. In Q(sqrt2), 6 has norm36 but is not square: (a+b sqrt2)^2=6 for rational a,b forces ab=0 and then a^2=6 or b^2=3. This auxiliary example is not asserted to be in the full source base field K_8; the actual conductor15 square-class obstruction above uses the correct K.

For comparison, at conductor7, the product of the three primitive D_j is 169=13^2, compatible with the already known exceptional identity. At conductor30 the primitive norm is 961. Exact Pell primitive parts through60 have square values only at7/30, but that finite fact supplies neither all-order square-class classification nor a proof of Conjecture10.

## Precise gaps and strongest falsifier

Missing: classify square classes over the full K for arbitrary composite n, then distinguish genuine unit relations from square-class dependencies, and impose the even-k cardinality condition. A uniform conductor descent could in principle proceed through primitive Pell factors and local valuations, but neither a required all-n odd-valuation primitive divisor result nor the unit-relation bridge is established. The Robinson square-value discussion in the source is a connection, not an equivalence permitting assumption of its conjecture.

Strongest current objection: this is an incomplete classical Kummer/Pell route whose prime cases are already public. It gives no qualifying discovery. The n15 calculation falsifies the simplest sufficient criterion at a nonexceptional input. Any claimed completed proof using independent radical flips for every nonexceptional n must first resolve that exact obstruction. No source counterexample, worldwide priority, novelty PASS, nomination, PROOF.md, Lean, paper or formal investment is warranted.

## Reproduction

Run `bash run.sh python3 check.py` (Python3 and SymPy). Exact resultants recover nine real cyclotomic polynomials/norms; polynomial remainder checks verify the n15 square and mod5 overlap; Pell divisor recurrence through60 and 24 already-public Fel recurrence evaluations are checked. Runtime about0.5s. Limits: AS512MiB, CPU210s, timeout230s with process-group TERM/KILL and BLAS1. These are bounded identity checks, never universal proof or numerical evidence.
