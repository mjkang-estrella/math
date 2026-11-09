# Ordinary proofs and stopping points

Discovery only; accepted credit 0. No mathematical enumeration, numerical experiment, solver, Lean or child agent was run. The two recurrence proofs below are complete ordinary classical reductions, not qualified new discoveries. The third sustained route is incomplete. No CANDIDATE.md or Pi execution request is justified.

## 317722: full positive-root reduction, zero credit

Raff 0809.2551, §6 Conjecture 2, means that an alternating-sign recurrence exists, not that every annihilator alternates. Multiplying an annihilator by an arbitrary polynomial would make the latter assertion false for trivial reasons. The 2009 thesis, Chapter 3, repeats the conjecture. The product is Cartesian, as the explicit grid definition confirms.

Let G be a connected simple graph on m vertices. Its Laplacian eigenvalues are 0, λ1,...,λ(m−1), with each λi>0. Put ai>1 with ai+ai^(-1)=2+λi. The matrix-tree theorem and the Cartesian Laplacian sum give, for n≥1,

    τ(G □ Pn) = (1/m) ∏i λi U_(n−1)(1+λi/2)
               = C ∏i (ai^n − ai^(−n)),
    C = (1/m) ∏i λi/(ai−ai^(-1)) > 0.

Here is the normalization, which cannot be omitted. The nonzero Pn eigenvalues μj have product n, because Pn has one spanning tree. In the full Laplacian product the zero-G eigenvalue contributes n. Division by mn leaves 1/m times ∏i∏j=0,...,n−1(λi+μj). The latter product equals λi U_(n−1)(1+λi/2). To see the Chebyshev identity without an unproved count bridge, the μj for j=1,...,n−1 are 2−2cos(πj/n); they are the roots after this substitution of the monic polynomial U_(n−1)(1+λ/2) in λ. The path eigenvectors sin/cos diagonalization or the tridiagonal determinant recurrence proves this identity. U0=1, U1=2+λ, and Uj=(2+λ)U(j−1)−U(j−2).

Expanding the product gives a finite linear combination ∑b cb b^n of positive real bases b=∏i ai^(εi), εi∈{−1,1}. Combine equal bases and discard zero coefficients. If B is the remaining set, then p(X)=∏b∈B(X−b) annihilates the sequence. Every elementary symmetric function of B is strictly positive, so the monic coefficients of p alternate strictly. Vandermonde independence of distinct nonzero exponential bases proves p is the minimum annihilator.

For completeness this is an integer, not merely real, recurrence. Each λi is an algebraic integer, and ai satisfies X²−(2+λi)X+1=0, hence is an algebraic integer and a unit. Every Galois automorphism permutes the λi and can interchange ai with ai^(-1), so it permutes the full set of bases. Since τn is rational for every n, uniqueness of its exponential representation makes the subset with nonzero coefficients Galois invariant. Thus p has rational algebraic-integer coefficients, hence integer coefficients. This argument also covers collisions and cancellations; multiplicative independence is unnecessary for signs. For m=1 the sequence is constantly 1, with annihilator X−1. For disconnected G, τn=0 for every n; X−1 is an alternating annihilator. Empty-graph conventions are irrelevant to the substantive assertion and supply no credit.

Disposition: complete matrix-tree, Chebyshev, exponential-annihilator bridge; zero credit under the campaign's classical-reduction rule. This is not an exclusion based on shortness alone, and does not claim an identified prior paper states this exact conjecture's answer. A full latest-journal/citing/correction audit was not completed; it cannot turn this excluded bridge into a novelty-qualified candidate.

## 317724: exact minimal order k, zero credit

For k≥2 the nonzero Kk eigenvalues are k with multiplicity r=k−1. The previous count identity becomes

    τ(Kk □ Pn) = k^(k−2) U_(n−1)(1+k/2)^(k−1).

Choose a>1 with a+a^(-1)=k+2. Expanding gives exactly k terms

    [k^(k−2)/(a−a^(-1))^r] ∑j=0,...,r (−1)^j binom(r,j) (a^(r−2j))^n.

All coefficients are nonzero; all bases are distinct because a>1. Therefore the minimum recurrence order is r+1=k: an annihilator must vanish at each base, by Vandermonde independence applied to the recurrence identity, and their product supplies the upper bound. Its coefficients are integers because a↔a^(-1) permutes these bases. For k=1 there is one spanning tree for every path and minimum order 1. The initial indexing n≥1 does not change linear independence or minimal order.

This resolves both existence and minimality, unlike merely applying Cayley–Hamilton to a Bell-number transfer matrix. It also distinguishes this target from r275's parked path-grid order conjecture 317723: there the different ai can collide multiplicatively; here there is only one a, so there is no unpaid noncollision lemma. Nevertheless this is a full routine specialization of the classical product formula, and earns zero credit. No Pi handoff.

## 317666: sustained projection-cone route, incomplete

Read source §3 Theorem 3.1's actual inequalities, common-refinement definition, Theorem 3.4, Examples 3.6–3.7, Theorem 3.8 lower-bound discussion and Conjecture 3.9. For a partition-lattice maximal chain F, the cone inequalities compare averages of d(i,j) on successive blocks Fk\F(k−1). A generic full-dimensional cell fixes which chains' inequalities hold. The target is the number of projection cones needed in an intersection representation of that cell; merely counting all feasible chains is a stronger sufficient route and must not be silently equated with the minimum number of necessary cones.

First route: encode each feasible chain by a permutation of its n−1 mergers, suggesting (n−1)!. This only counts rankings after fixing an underlying rooted tree. Different compatible chains can have different tree topologies; the source's n=3 maximal cell with two cones already exhibits this. Thus no fixed common tree and no injection have been proved. A valid next lemma would assign every essential cone of an arbitrary cell an injective permutation label independently of topology.

Second route: delete a distinguished leaf, restrict the data, and seek a recurrence c(n)≤(n−1)c(n−1). A binary-tree insertion has several edge choices, not automatically n−1 compatible choices, and restriction changes both denominators and numerators in the average inequalities. A chain feasible for d need not be shown feasible for the naively restricted cell. The required compatibility map and uniform fibre bound remain unproved. Theorem 3.4 about optimal least-squares trees is insufficient: it guarantees a best tree in some cone containing d, not a bound on all essential cones.

Third route: choose an irredundant inequality representation and charge each necessary cone to a facet. This does not give the factorial bound: the source cone has n−2 inequalities but its common refinement may have many distinct supporting hyperplanes. No dimension-only Helly argument bounds the number of cones whose intersection equals a prescribed chamber. Helly controls emptiness, not exact chamber equality. Park without a witness or complete finite route; no solver architecture proposed.

## 319360: exact degree-condition route, incomplete

The source's missing MathDB theorem labels are Theorems 4.6 and 4.3, Conjecture 4.8. Read the full numerical conditions and proof of 4.3 near Lemmas 4.4–4.5. The classical toughness-to-factor theorem 4.7 proves that all realizations have a factor; it does NOT prove that their sequence passes this particular sufficient test. The source itself says 4.3 is not best monotone, with an explicit sequence passing 3.1 and failing 4.3. Thus semantic implication of graph properties does not settle the target about tests.

For an attempted contrapositive fix a,b,q violating 4.3, r=a+k+q−2, s=n−max(0,b−k+1)−max(0,q−1)−1. Its failure supplies d(n−a)≤max(r,s), together with either db≤r or d(n−a−b)≤s and a low prefix sum. One would need i with k≤i<kn/(k+1), d(floor(i/k))≤i, and d(n−i)<n−floor(i/k), contradicting 4.6. Choosing i=a alone supplies neither the correct low-index bound nor the allowed range; choosing i=max(r,s) loses the required high-index bound because n−i need not be n−a. Neither condition is pointwise comparable in these parameters. Missing lemma: a graphicality-aware conversion of every such (a,b,q) into a forbidden i, or an explicit graphical sequence satisfying all 4.6 inequalities and failing 4.3. No such lemma or witness established. Park, not exclude by the classical factor theorem.

## Explicit public resolutions and corrections

317604: Füredi–Gerbner–Vizer, European J. Combin. 48 (2015), 224–233, §1.6 Lemma 1.9 and Corollary 1.10 prove precisely the sufficiently-large-n statement, including equality. For a t-multiset T, if some F lacks T, every member containing T must contain an extra occurrence from F\T. Hence this subfamily is O(n^(k−t−1)). Fixing any member and covering the entire family by its at most binom(k,t) t-submultisets gives the same lower-order bound unless some T is common to all. A trivial family has binom(n+k−t−1,k−t) members; thus an extremum is exactly a full t-star for large n. The k=t case is immediate. This is the actual printed proof, not just a cited abstract; zero credit.

317646: Harcos–Károlyi–Kós 1004.0253, Theorem 3 and §2 pp.3–5 are an actual public full proof of the exact odd-order group theorem. Additive and multiplicative notation are isomorphic here, not different hypotheses. Their character expansion in characteristic two and unique-monomial Lemma 4 give a nonzero determinant; absence of a distinct matching would make every summand vanish through repeated rows. Theorem 1 proves the stronger character determinant assertion. No novelty; zero credit. A fresh journal/corrections audit is unnecessary for rediscovery credit once this earlier full proof is read, but is not represented as completed.

316980: Wotzlaw 2009 thesis, printed pp.72–74, Theorem 4.6.1, Lemma 4.6.3 and Corollary 4.6.4 give exactly both connectivity ranges. The lemma converts the source CM cell complex to a normal graph complex; the theorem glues surviving faces through a strong facet chain. Corollary 4.6.4 explicitly names Athanasiadis Conjecture 6.2 and repeats the MathDB bounds. Do not mistake the preceding broader graph-manifold Conjecture 4.6.2 for the target. Zero credit.

317342: Diao Definitions 1.1–1.2 recover the missing F,G. Even-Zohar 1108.4902, Theorem 2 and Corollary 14 (printed p.9) explicitly prove the F piecewise-linearity conjunct. G is a nondecreasing positive integer by its definition, and finite for finite K by the source's bounds. On any bounded K interval it has only finitely many changes, since its total variation is bounded by its finite integer endpoint values. Thus G is constant on the intervening open intervals (endpoint values must be recorded separately). Under the usual piecewise convention this is the full remaining routine bridge; if a stricter convention demands half-open continuity, that extra endpoint claim is not proved here. Zero credit either way: public F resolution plus elementary integer-monotonicity bridge, no new full endpoint qualified. The 2012 journal body and all correction literature were not fully audited.

317350: the intended Z/2 tight-neighborliness conjecture is publicly resolved, as Datta–Murai's introduction and Corollary 4.4 proof record, with dimension 3 supplied by Burton–Datta–Singh–Spreer (also printed as Theorem 2.4 in 1511.04500). Literal arbitrary-field wording needs orientability: tightness over odd characteristic cannot silently be substituted for Z/2 tightness. No new resolution of a domain ambiguity; zero credit. All historical original proof dependencies were not fully read, so this exclusion is qualified as public intended resolution plus fidelity hold.

318040: source §1.1 has only edge coordinates; Xi=∑j≠i x{i,j} is a derived degree linear form. Treating Xi as independent vertex coordinates changes the ring's dimension. Also ∑Xi=2∑xij, so the displayed first degree-one functions are dependent; source systems are understood as a set with the shared invariant removed. The literal independently-adjoined-variable reading has too few parameters for dimension binom(n,2)+n. That is a domain/transcription issue, not a significant counterexample to the intended invariant-ring conjecture. No full intended nullcone witness proved; zero credit.

319348: source Conjecture 2.2 explicitly requires a good connected affine structure, with uniqueness only up to isomorphism; it warns that type A1 needs extra hypotheses and that three-factor multiplicities obstruct literal uniqueness. Relabelling classical components can conjugate promotion without changing the affine isomorphism class. That is no substantive counterexample to the intended question. No rigidity proof for arbitrary factors or genuinely nonisomorphic valid structures; park.

## Remaining exact gaps

319291: source Conjecture 7.2 gives the precise replacement operation and equivalence to the lead costing at most one trick. Strategy stealing valid in one suit fails when a lead forces a discard in another suit. A statewise simulation preserving legal follow-suit moves and trick balance is missing. Single-suit theorem is not a full answer. No game search.

319346: unlabelled rows are orbit sums of labelled rows, so labelled independence implies the unlabelled assertion in characteristic zero. This does not prove the labelled assertion. An extension-choice matching gives only structural rank; actual all-ones minors can cancel. Missing a nonsingular minor with controlled sign or an explicit rational dependence. Do not use numerical rank tables as a proof.

339277: two universal claims, including odd-order full transversals. Near-full or asymptotic partial transversals do not settle the conjunction. No exact universal augmentation mechanism or finite obstruction; park flagship promptly. No current-open certification from stale metadata.

317478,317479,317480: source Conjectures 1.2,1.4,1.8 require all iterates, not first-order inequalities. RSK/Gessel counts give the underlying finite polynomials, not iteration-preservation. For 317478 a real-rootedness route would require that property for every Pn; it is not supplied. For the q-convex claims a moment representation with coefficientwise positive minors and closure under iteration is missing. Crossing number is maximum mutually crossing arcs, not total arc-pair crossings; Touchard–Riordan's usual statistic cannot be substituted. The additional log-concavity clause in 317480 is not discarded. No enumeration, no claimed counterexample, no inference from a first-order LIS predecessor to infinite log-concavity.

317512: settlement supplies surjectivity of representation-ring maps, not that the kernel is generated by equalities between existing cross-ratios. Determinantal extension relations can impose higher-degree relations. Need an ideal equality, or a concrete settled 3-connected extension with a proved inequivalent kernel; neither supplied. No symbolic solver.

317864: positive scalar eigenvalues of the weighted Laplacian imply positive real determinant values for positive weights, not positive coefficients in the graph basis. In exp(r), negative cyclic terms of log φ can interact with disconnected products. A sign-reversing cancellation or positive graph expansion in all degrees is missing. Printed graph pictures were not visually audited; no coefficient witness claimed.

317985: source Corollary 5.16 proves q-symmetry, Conjecture 5.17 asks q-unimodality at fixed cycle type, descents and excedances. Henderson–Wachs Theorem 1.2 proves a different t-unimodality after a q-shift; that cannot be used as the resolution. Need an injection on fixed (λ,d,j) major-index fibres or a valid Lefschetz grading preserving all those constraints. No such mechanism established; park with journal/citing gap.
