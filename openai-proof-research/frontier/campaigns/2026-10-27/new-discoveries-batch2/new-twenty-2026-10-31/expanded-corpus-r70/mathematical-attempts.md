# Mathematical attempts and remaining obstructions

No full new endpoint is established. All computations here are diagnostics, not Lean certificates. The three sustained routes were 375489, 375075 and 375345. The fractional q-binomial route also received an exact coefficient sweep.

## 375489: exact abstract chain optimization

The source Section 4 defines nu(s) as the minimum size of the closed grid neighborhood of an order ideal of size s, and a nu-chain by c_(l+1) >= nu(c_l). We enumerated every weakly decreasing row-length vector in each tested rectangular box. For row lengths r_i, the closed neighborhood has row length max(min(n,r_i+1) when r_i>0, r_(i-1), r_(i+1)), with missing rows zero. This computes the actual minimum, without presuming that antidiagonal initial segments are isoperimetric.

For N=mn and f(s)=min(s,N-s), Bellman's recurrence is F(N)=0 and F(s)=f(s)+max{F(t): max(s+1,nu(s))<=t<=N}. On a connected box every nonempty proper set has a larger neighborhood, so no positive-reward cycles are omitted. Starting at any positive s checks a relaxation including every nontrivial source chain; zero and full endpoints contribute zero. All 74 boxes with 2<=n<=min(m,7), 2<=m<=16 and m+n<=22 were completed, enumerating 832,167 ideals in total. Every optimum equals the antidiagonal objective. The maximizing size chain is saved for each box.

A proof still needs a uniform Bellman supersolution B_(m,n)(s) with B(s)>=f(s)+B(t) for every t>=nu(s), and a bound on its largest starting value by D(m,n). Pointwise smallest growth alone does not prove the objective bound, since f decreases after the median. Thus the source's isoperimetric observation cannot simply be substituted as a finished proof. A search lead describes a convex-order proof for realizable Lipschitz functions but expressly disclaims the stronger abstract chain conjecture. It is retained as an unread original-proof lead, not a subsumption or novelty clearance.

## 375075: exact extremal parity, not parity of a constructed family

Subsets with size congruent to a form the vertices of a compatibility graph; edges join distinct sets with intersection size congruent to a modulo k. Maximum town size is exactly maximum clique size. The bitset search uses a greedy proper coloring of each candidate induced graph to bound clique extensions, then exhaustively branches. It returns both an attained family and an upper-bound search result. Completed instances cover all n<=10, n>=k+a, and additionally (11,2,0), 116 triples total. No odd maximum occurred. The internal 100-second cap was checked after each instance; n=11 is not completely covered.

The source's Proposition 5.2 proves the case a=0, n=0 mod k: complementing a member preserves compatibility with all members, so maximality forces complement pairs. This already-known special case is not a new result. For arbitrary residues, complementation changes cardinalities to n-a, so it is not an involution within the same class. Translating by symmetric difference with a fixed family member converts an (a,a)-family to a (0,0)-family, but does not automatically preserve extremality in the latter class or yield closure under further translations. A general free involution on an extremal family, or an odd exact maximum outside the tested range, is missing. No cardinality construction alone can establish an odd *maximum*.

## 375345: degree-four matching/weight route

The source definition is the minimum size of a maximal matching, not maximum matching. Atlas checks enumerate all matchings and test maximality by edge domination. The larger sample uses the exact recurrence: choose an edge uv; every maximal matching contains an edge ab incident to u or v. After choosing ab, the remaining matching must be maximal in G-{a,b}, and conversely. Therefore mu*(G)=1+min_ab mu*(G-{a,b}) over those incident edges. Memoization on the remaining vertex bitmask gives an exact value for each sampled graph.

The 461 connected subquartic atlas graphs through order seven and 911 seeded connected graphs of orders 12 through 28 gave no violation. The larger collection starts with random labeled trees of maximum degree at most four and adds edges subject to the degree cap; it is a structured sample, not exhaustive graph coverage. The full seed and generator are saved.

The elementary bound H>=|E|/4 loses the needed information even on triangles; it cannot establish the conjecture by an edge-count estimate. A prospective charging proof would choose a locally minimal maximal matching and allocate incident harmonic weights to its edges. Degree-four regular regions are harmless because H=n/2 and every matching has at most n/2 edges. The unresolved step is a charging inequality across irregular boundaries, with a proved local matching-exchange condition. No such inequality has been established. Source provenance is the surviving degree-four restriction of a TxGraffiti conjecture; the old unrestricted counterexamples and parameter variants are not candidates.

## 375048: exact rational exponent projection

The numerator is expanded by subset size s and sum of chosen indices. Only s*r integral survives the integer trace, because the denominator has only integral exponents. The numerator term has sign (-1)^s and degree s*r+sum(indices). The denominator inverse is the partition-number DP for parts at most k. We compared all degrees 0..350 for k=1..18 and all 232 distinct reduced rationals 0<r<=4 with denominator at most 13. No violation occurred. This does not control the eventual polynomial/quasipolynomial coefficient tails. For odd denominators, both signs survive; dropping negative terms only gives an upper bound and does not by itself produce a domination injection. The full all-degree inequality remains unproved.

## 375572: paired Nahm coefficient check and tail justification

For the even exponent E, minimizing the real quadratic over the other two variables gives E>=a^2/2-1/2, E>=j^2/4-1/2, and E>=(2s^2+2s-1)/3. For the odd exponent the corresponding bounds are a^2/2-1, j^2/4-1, and (2s^2+4s-1)/3. These follow by completing squares; minimizing over all real variables is a valid lower bound for nonnegative integer indices. Thus any a,j, or s greater than 20 contributes beyond degree 40. Denominator expansions contain only nonnegative powers. The theta exponent is 6r^2-2r (even identity) or 6r^2-4r (odd identity), so the saved bilateral cutoff also includes all contributions through degree 40. The exact two coefficient arrays agree through degree 40. No all-degree identity or Lean theorem follows from this check.

## Other finite checks and limitations

The two-circuit cubic search fixes each pair of cycle lengths through total order 10, enumerates all complementary perfect matchings avoiding cycle edges, tests every cut for cyclic 4-edge-connectivity, excludes Petersen up to isomorphism, and checks four-cover existence by pairing unions of perfect matchings. This includes all source-eligible graphs at these orders up to relabeling, with duplicates allowed. There is no new witness.

All nonisomorphic trees through order 14 were grouped by diameter, with every tied Wiener maximizer checked for intersection of center and median. Small multigraphs use exact edge coloring for every connected labeled multiplicity assignment 0..2 through order four. Other atlas tests and their limited scopes are specified per ID in outputs/search-coverage.json.

The early-search requirement is still incomplete for normal plane cycle sets, the cohomological tensor map, knot/tri-plane invariants, and general finite Coxeter systems. These have explicit definition/checker gaps, not negative search results. Asymptotic thresholds, bounded hereditary classes, unspecified big-O constants and nonrationality of infinite series cannot be refuted by one fixed finite instance; their entries retain their quantifier obstructions. No global coverage or novelty certification is claimed.
