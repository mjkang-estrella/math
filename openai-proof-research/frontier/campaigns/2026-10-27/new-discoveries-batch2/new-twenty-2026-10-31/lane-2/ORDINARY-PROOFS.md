# Lane 2: ordinary mathematics and failed routes (zero credit)

These are research notes, not an accepted solution or Lean certificate. No Lean theorem, axiom audit, independent review, or extracted rebuild is claimed.

## 319825: complete ordinary reduction, excluded as a routine classical consequence

**Exact primary target.** Novaković–Singer–Singer, arXiv:1004.4014, Section 5, Conjecture 5.1, Eq. (19), PDF p. 9. The journal numbers this Conjecture 1. Definitions are in Eqs. (3)–(7), (11), and (15). Set r=floor(d/2), t_j=N^d((d+1)/2+j), with N^d the normalized cardinal B-spline (support [0,d+1]). Symmetry gives t_{-j}=t_j. The displayed periodization has first row (t_0,...,t_r,0,...,0,t_r,...,t_1), for admissible orders with no overlap (m>=2r+1). Its Fourier eigenvalues are

    F_d(2πk/m),  F_d(θ)=t_0+2 Σ_{j=1}^r t_j cos(jθ),  0<=k<m.

The assertion is positive definiteness and a minimum at k=m/2 (even m), or k=(m±1)/2 (odd m). For d>=2 the following proves the full assertion for every admissible m. At d=1 the symbol is the constant 1, so the named locations are minimizers but not unique. This is not used as a wording counterexample.

**Why the first shortcut is insufficient.** Merely knowing t_0>t_1>...>t_r>0 does not prove that F_d is decreasing on [0,π]. For example 1+0.8 cos θ+0.6 cos(2θ) has decreasing positive coefficient magnitudes, but derivative -sin θ(0.8+2.4 cos θ) changes sign inside (0,π). Its minimum is not at π. A coefficient-shape heuristic therefore does not prove the source conjecture.

**Classical replacement route.** Define the Euler–Frobenius polynomials by

    P_{d,ρ}(z)=(1-z)^(d+1) Σ_{k>=0}(k+ρ)^d z^k.

This is a polynomial. Coefficient extraction gives

    [z^k]P_{d,ρ}= Σ_{l=0}^{k} (-1)^l binom(d+1,l)(k+ρ-l)^d.

By the source truncated-power formula for N^d,

    N^d(k+ρ)=[z^k]P_{d,ρ}/d!                  (0<ρ<=1).

Terms with l>k vanish for ρ<1; at ρ=1 the additional l=k+1 term is zero for d>=1. This is also Janson (2013), Theorem 3.2 and Eq. (3.11). It identifies the exact object, rather than a similarly named spline polynomial. For d=2s use ρ=1/2; for d=2s+1 use ρ=1. In both cases, with r=s,

    P_{d,ρ}(z)=d! Σ_{j=-r}^{r} t_j z^(j+r).             (1)

All zeros of these polynomials are real, negative and simple: Janson, Remark A.2, with the endpoint ρ=1 having degree d-1 rather than d. Here is the full elementary argument behind the needed special cases. Differentiating the generating series gives

    P_{d+1,ρ}=(ρ+(d+1-ρ)z)P_{d,ρ}+z(1-z)P'_{d,ρ}.   (2)

For 0<ρ<1, P_{0,ρ}=1, P_{1,ρ}=ρ+(1-ρ)z, and degree d has positive leading coefficient (1-ρ)^d and positive constant ρ^d. If P_d has ordered simple negative roots b_1<...<b_d, then at each b_i the value of P_{d+1} is b_i(1-b_i)P'_d(b_i), so its sign is (-1)^(d-i+1). The sign at negative infinity is (-1)^(d+1) and the sign at 0 is positive. The intermediate value theorem yields one root in each of the d+1 disjoint intervals (-infinity,b_1),(b_1,b_2),...,(b_d,0). Degree d+1 exhausts all roots, and makes them simple. For ρ=1, start with P_{1,1}=1 and P_{2,1}=1+z. A degree d-1 polynomial P_{d,1} has positive leading coefficient 1; (2) has degree d and positive leading coefficient d-(d-1)=1. The same sign argument, now with d-1 old roots, gives d simple negative roots. This proves the endpoint separately, without incorrectly retaining degree d.

By (1), the relevant polynomial is reciprocal of even degree 2r, with positive leading coefficient c. Its roots therefore occur in reciprocal pairs -a,-1/a, a>0. None is -1: reciprocal pairing of the remaining roots and simplicity would contradict the even degree if -1 occurred. We may choose a>1 from each pair, obtaining

    P_{d,ρ}(z)=c ∏_{i=1}^r (z+a_i)(z+a_i^(-1)),  a_i>1.

On z=e^{iθ}, (1) consequently becomes

    F_d(θ)=(c/d!) ∏_{i=1}^r (a_i+a_i^(-1)+2 cos θ).   (3)

Every factor is strictly positive, since a_i+a_i^(-1)>2. Each decreases strictly with θ on [0,π]. Their product is strictly decreasing when r>=1. Evenness and 2π-periodicity then put the sampled minimum precisely at the grid locations nearest π, yielding both formulas of the source. The positive Fourier spectrum proves positive definiteness of the real symmetric circulant.

**Adversarial checks.** The half-integer samples for even degrees use ρ=1/2, not the ordinary Eulerian polynomial P_{d,1}. The odd-degree polynomial has degree d-1. The normalization is 1/d!, not 1/(d+1)!. Reciprocal factors have a plus sign in 2cos θ. Simplicity, not symmetry alone, excludes a root -1. Orders for which the two circulant coefficient blocks collide are not silently substituted into the displayed row convention. Positivity alone would not identify the smallest Fourier mode; (3) does both. No numerical approximation is used in this proof.

**Significance and disposition.** This does resolve the ordinary intended source assertion, but its entire bridge is a classical same-object spline/Euler–Frobenius identity, the classical negative-simple-root theorem, and reciprocal factorization. Janson explicitly states the first two and cites older antecedents; they are not newly proved discoveries here. Under the explicit campaign exclusion of routine corollaries, this is not nominated for credit or expensive formalization. No earlier paper explicitly printing the final circulant statement is asserted. Current primary publication status beyond the read preprint and the bounded searches is not certified. The old MathDB reference claiming a 1988 refutation concerns the general de Boor conjecture in the introduction, not Conjecture 5.1: it is not treated as a refutation of this target.

**Lean feasibility.** A formal project would need the finite truncated-power/sample identity including ρ=1, interlacing/root enumeration with multiplicities, reciprocal-root pairing, a real trigonometric product identity, and a discrete Fourier diagonalization/positive-definiteness bridge for the exact row convention. No literal Lean endpoint currently exists. Supplying only a generic positive-product monotonicity lemma would leave all of those mathematical bridges and earn zero credit. This lane deliberately does not produce a partial formalization of an excluded routine consequence.

## 320868: exact scope restoration; compression obstruction; unresolved

Primary arXiv:1012.3918, p. 2 defines Boolean subfamilies by *ambient union and intersection*, not merely poset isomorphism. Section 5, Conjecture 5.1, p. 7 proposes that among m=2^n sets, 2^[n] maximizes the number of d-dimensional Boolean subfamilies. Throughout the nontrivial problem, d>=2. The d=1 chain objection is not a substantive resolution. The manuscript's running date is November 10, 2018 although its arXiv banner is v1, 17 December 2010; no distinct revision chronology is inferred from that date.

For d=2, count unordered incomparable pairs A,B for which A∩B and A∪B both belong to the family. Each counted pair determines a unique four-set Boolean square. Conversely, each Boolean square has one such middle pair, so this count is exact.

For the full Boolean lattice, use four coordinate states: outside the top, in the bottom, in first atom, in second atom. Each atom must be nonempty. Inclusion–exclusion and division by 2 for exchanging atoms give

    b_2(2^[n])=(4^n-2*3^n+2^n)/2.

More generally for d>=2 the analogous count is

    b_d(2^[n])=(1/d!) Σ_{j=0}^d (-1)^j binom(d,j)(d+2-j)^n.

The d atom blocks are nonempty and unordered. The bottom and outside blocks may be empty. This follows directly from the union/intersection definition, and does not rely on the source's informal atom paragraph, which calls all atoms nonempty including the bottom. Restricting the bottom to be nonempty would contradict the given Boolean-lattice example.

**Failed proof route, with exact obstruction.** Ordinary downward coordinate compression need not preserve or increase b_2. On ground set {0,1,2,3}, encode sets by bit masks. Take

    F={0,1,2,3,4,5,7,8}.

Compression in coordinate 0 changes 7 to 6 and leaves all other masks fixed. The five incomparable pairs completing squares before compression are

    {1,2}, {1,4}, {2,5}, {3,4}, {3,5}.

The three after compression are

    {1,2}, {1,4}, {2,4}.

Thus a general compression-monotonicity lemma is false even in this tiny setting. The calculation is exact and can be verified by the above intersection/union criterion. It is an obstruction to a proof strategy, not a counterexample to the conjecture (both counts are below 9, the Boolean optimum for eight sets).

**Continuation beyond that failure.** Closing the family under union and intersection can only increase its square count, but does not preserve its cardinality, so it does not reduce the conjecture to a lattice extremum. The alternative pair-injection approach bounds the count by the number of unordered incomparable pairs, at most binom(m,2), but at m=2^n this is of order 4^n/2 without the necessary negative 3^n term; it cannot prove the exact assertion or control higher-dimensional copies. No exact-cardinality closure replacement or global injection emerged. The formula for b_d above is only the benchmark, not an upper bound for arbitrary families.

The exhaustive diagnostic in boolean_diagnostic.py checks all 1,820 four-element and all 12,870 eight-element subfamilies of 2^[4]. Maxima are 1 and 9 respectively. This tests only one ambient ground set, two cardinalities, and d=2. It is not a universal proof, nor Lean-checked. General n,d and arbitrary ambient ground sets remain unresolved.

**Formalization bottleneck.** The square-count definition and the obstruction are small finite Lean tasks, but formalizing them would not solve the conjecture. The missing universal extremal inequality remains an ordinary mathematical gap. No source-statement endpoint exists, no acceptance is requested.

## 321049: restored full source; exact A-type reduction and finite diagnostics; unresolved

Primary Ershov–Jaikin-Zapirain–Kassabov author manuscript 2015gradedT0729.pdf, Section 4, Definitions pp. 20–25 and Conjecture 4.14 p. 27. Here “classical” means the integral-reflection root-system axioms, NOT merely A/B/C/D. Fact 4.1 includes E6,E7,E8,F4,G2 and nonreduced BC_n. Rank at least 2 and irreducibility are mandatory. The desired uniform conclusion is diameter Γ_s<=3 for all these systems.

Vertices are Borel root sets Φ_f defined by generic linear functionals. For a reduced classical system the boundary is its simple-root base and the core C_f is the positive set minus its simple roots. Adjacency of f,g requires witnesses f',g' such that

    Φ_f \ Φ_g ⊆ C_{f'},   Φ_g \ Φ_f ⊆ C_{g'}.

Because every root has exactly one sign, these difference sets are negatives. Since C_{-h}=-C_h, the two witnesses can always be chosen opposite: adjacency is equivalent to the first difference being contained in *some* Borel core. This removes a redundant existential but does not prove the diameter bound.

For A_(N-1), a Borel is a total order of the N coordinate labels. Fix the identity order. For another order p, let D be the roots e_i-e_j with i<j whose label order is reversed in p. A root e_i-e_j is positive but not simple in an order q precisely when i precedes j with at least one label between them. Therefore adjacency to the identity is exactly existence of a topological order q for D with no consecutive pair linked by an edge in D. This is an exact combinatorial criterion; treating simple-root adjacency alone as the Weyl-graph adjacency would build a different graph.

The diagnostic uses dynamic programming on (placed-label mask,last label), checking predecessors and forbidding a D-edge from last to the new label. It then builds the corresponding permutation Cayley graph and performs BFS. Results: A2 has 6 vertices, degree 2, diameter 3; A3 has 24 vertices, degree 10, diameter 2; A4 has 120 vertices, degree 58, diameter 2; A5 has 720 vertices, degree 369, diameter 2. The program is finite exact Python, not a kernel-checked certificate.

**Two attempted continuations.** (i) The source's induction increases the Borel intersection by passing through an intermediate vertex, but concatenates two paths; it supplies connectivity, not an upper bound 3. No rank-independent control follows by simply repeating it. (ii) At A5 the generator set has more than half the group elements; any set S in a finite group with |S|>|W|/2 satisfies S∩wS^(-1)≠empty for each w, hence gives paths of length at most two. However A3 and A4 have fewer than half the elements as generators, and no uniform large-rank density bound has been proved. A good order on N labels cannot simply be extended by appending label N+1: a required edge from the old final label to N+1 would become simple and invalidate the core condition. Thus the empirical density argument does not provide induction. The B/C/D signed-order families and the exceptional/nonreduced systems would need independent work even if this A-type density question were settled.

**Formalization bottleneck and disposition.** A complete result would need the source's root-system convention, Borel/core definitions, adjacency, root-system classification or a classification-free construction, and a uniform three-step witness. A finite A2–A5 Lean computation would be a parameter-instance result excluded from discovery credit. No full proof or full-source Lean endpoint exists; park with the precise uniform core-covering problem open. No exact prior resolution was located in the bounded searches, which does not establish novelty.
