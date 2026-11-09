**H003 independent mathematical and cost review**

**Verdict: accept the narrow cardinality theorem; reject the inference from compact local constraints to a fixed-exponent enumeration saving.** The draft's three mathematical claims are correct under its stated hypotheses, including uniformity over arbitrary choices of distinct odd primes. No substantive counterexample to those claims was found. The concrete bypass reviewed below is an exact, output-sensitive two-list interval query. It works, but is already covered by Hittmeir's prior art and supplies no supported disruptive factoring improvement. Verified new algorithmic improvement: **NONE**.

This review reads the complete H003 preregistration, cardinality draft, diagnostic source and original JSON, together with AGENTS.md and the research contract. It does not change the preregistration, evidence, solver, shared research state, or formal specifications. All computational checks described below ran in memory, with bytecode writing disabled, inside this project. They are diagnostic checks, not a new factoring benchmark or a formal proof.

**Mathematical audit.** Write chi for the Legendre symbol, let ell be an odd prime with ell not dividing N, and include zero among the allowed discriminants. The map

    (s,y) -> (u,v) = (s-y,s+y)
    (u,v) -> (s,y) = ((u+v)/2,(v-u)/2)

is a bijection over F_ell between y² = s² - 4N and uv = 4N. There are ell-1 such pairs: u can be any nonzero element, then v is forced. There are z = 1 + chi(N) pairs with y=0, since 4 is a nonzero square. Each other allowed s has exactly two distinct y values. Thus

    ell - 1 = z + 2(|R_ell| - z) = 2|R_ell| - z,
    |R_ell| = (ell + chi(N))/2.

This proves the formula without a randomness assumption, a character-sum estimate, or a factorization of N. The minimal case ell=3, chi(N)=-1 gives one allowed residue and density 1/3. Generally (ell-1)/(2ell) >= 1/3, so the local density bound is valid.

For distinct primes ell_1,...,ell_k, the CRT bijection from Z/MZ to the product of the local fields restricts to a bijection between R_M and the Cartesian product of their allowed sets. Consequently

    D := |R_M| = product_i |R_ell_i|,
    M / 3^k <= D <= M,       M = product_i ell_i.

The product identity is an exact bijective count. It neither assumes nor establishes probabilistic independence within a short interval of integers.

Order the primes increasingly and index from i=1. Distinctness and oddness imply ell_i >= i+2; hence

    M >= product_{i=1}^k (i+2) = (k+2)!/2.

For large k, this implies log M >= floor(k/2) log(k/2). Here and below logarithms in asymptotic arguments are natural. To make the uniform quantifiers explicit, fix epsilon>0. Choose K so that, for k>=K,

    k log(3) / [floor(k/2) log(k/2)] < epsilon.

For k<K, take M sufficiently large that K log(3)/log M < epsilon. These two cases cover every k, including sequences in which k oscillates between small and large values. Therefore there is an M_0(epsilon), independent of N and of the selected primes, such that

    M >= M_0(epsilon), gcd(N,M)=1  ==>  D >= M^(1-epsilon).

Together with D<=M this proves log D/log M -> 1 uniformly. One can also invert the factorial bound to obtain k=O(log M/log log M), uniformly for large M, and hence

    D >= M exp(-O(log M/log log M)).

This stronger explicit form does not need a theorem about the distribution of primes. The draft's weaker limit is sufficient. If log M/log N -> theta>0, then log D/log N -> theta; in particular complete enumeration cannot have an O(N^(theta-epsilon)) output count for any fixed epsilon>0.

**Scope qualifications and edge cases.** These are clarifications to preserve when accepting the draft, rather than objections that invalidate its theorem.

- Complete enumeration forces at least D individual outputs. It does not force D simultaneously stored residues: a generator can stream them. In a conventional fixed-width representation the output alone contains D ceil(log2 M) bits; the weaker Omega(D) work bound already suffices here. Neither bound applies to returning a compact formula or to finding one useful residue and stopping.
- For k=0, M=1 and the empty CRT product contains one residue. The logarithmic ratio is undefined there; the limit is about M tending to infinity with k>=1. Bounded k with growing primes is explicitly covered.
- If ell divides N, every s passes because s²-4N=s² modulo ell; the displayed local formula is inapplicable. On a promised composite input, a prime ell dividing N is a proper factor and should be returned. Test individual primes, or handle gcd(N,M)=N properly: a single gcd with a product of primes need not be a proper factor. At ell=2, both the invertibility argument and the formula fail.
- N need not be semiprime for the counting theorem. It holds for every integer unit modulo M, including squares and prime inputs. If N is an integer square coprime to M, all its local symbols are +1. This is consistent with the upper cardinality product; it is not a hard factoring instance.
- For odd N a genuine positive factor sum is even. Appending the allowed class 0 modulo 2 to the odd-prime constraints gives D classes modulo 2M, a constant density change. The discriminant-square condition modulo 2 by itself does not enforce this parity. Fixed additional parity restrictions do not change the exponent argument.
- Local acceptance is only necessary. To recover a factor, require s>=ceil(2sqrt(N)), test that s²-4N is a nonnegative integer square y², check integrality of (s-y)/2, and validate 1<d<N and N mod d=0. In particular s=N+1 represents the trivial decomposition. Negative or too-small residues, odd s, and false local positives cannot simply be declared factors.
- Short intervals, decision/counting queries, early success, extra coupled equations, repeated prime powers, and compressed representations retain exactly the exclusions stated in the draft. In particular, M need not be comparable to the factor-search width. Choosing a huge M increases available local information and also changes the cost of a proposed query; the theorem by itself does not settle that tradeoff.

The corrected operative statement is: **for every fixed epsilon>0, complete explicit enumeration of these CRT residue sets eventually emits at least M^(1-epsilon) items, uniformly over coprime N and distinct odd primes.** This is a lower bound on a specified output task, not on factoring, working memory, or every possible use of the constraints.

**Audit of the finite evidence.** The exact original files inspected have hashes:

    sieve_cardinality.py
    522506445206d6500b4dbc34599a7808b8ae64b906c581a895a687b5b6d8a15c
    result.json
    de26bd13e600698fb93ed42c947a39cc348d761f4ddeba78f21730b1d7c549aa

The source hash agrees with the JSON. The source generates its primes by exact trial divisibility; constructs the complete square set, including zero; applies Euler's criterion only to nonzero residues; and uses the correct CRT update

    r + m * (((s-r) * inverse(m modulo ell)) modulo ell).

This lies in [0,m*ell), agrees with r modulo m and with s modulo ell. The source checks uniqueness, range, and product count at every explicit stage. It additionally compares whole sets with direct filtering at its first five stages. Its lack of that last comparison at stage six is a declared coverage limit, not a failure.

I independently obtained each local set as

    {x + N*inverse(x) modulo ell : 1 <= x < ell},

and compared it with the discriminant implementation for all 266 prescribed nonzero residues. I reconstructed the original CRT updates and checked complete set equality against this independent filter at **all 12 stages**, extending direct equality through modulus 255255. All matched. In particular the final cardinalities are 2520 and 1620, and cumulative pair-merge counts are 2851 and 1839, for N=10403 and N=1022117 respectively. All seven counts-only rows and their integer inequalities also recomputed correctly; displayed floating logarithms agree within rounding.

The counts-only minimum and maximum are products of the permitted local extrema, for N coprime to the chosen modulus. They are not continued sieve runs on either of the two explicit N values. This distinction matters when later primes divide one of those inputs. Those rows perform arithmetic on cardinalities, not construction of the corresponding enormous sets. Their finite logarithmic ratios support code checking, not asymptotic curve fitting.

The recorded 0.009098204-second measurement is the source's internal timer through prime generation, checks, and construction of the result dictionary. JSON serialization/writing, final printing, and process startup are outside it. Pair merges also omit the cost of integer operations, sets, lists, and allocation. Nothing here measures a competitive splitter or certified bit complexity. The original evidence was not overwritten.

Both declared inputs are particularly unsuitable for a factoring-speed claim: the ordinary Fermat baseline starts at a=102 and a=1011 respectively, and a²-N is already 1 and 4. Both terminate on their first square test. This does not compromise a combinatorial cardinality diagnostic, which is the preregistered claim.

**One concrete bypass: an exact two-list CRT interval join.** The following analysis prices a real algorithm, not a subset-sum oracle. Let I=[L,L+W) with integer endpoints, 0<=W<=M, and let K be the number of accepted integers in I before optional parity filtering. Larger intervals can be decomposed into periods, with all repeated outputs charged. For factoring, L and W must be computed from N or a public search schedule, not supplied from hidden factors.

For each selected prime define the known CRT coefficient

    e_i = (M/ell_i) * inverse(M/ell_i modulo ell_i).

Partition the local sets into two groups. Form lists X and Y of all group contributions sum(e_i*r_i) modulo M, taking one r_i from each local set in that group. Let their sizes be A and B. Every tuple has a unique residue even within one group, because reduction modulo that group's primes recovers its choices. Therefore

    A = product_{i in group 1} |R_ell_i|,
    B = product_{i in group 2} |R_ell_i|,
    A*B = D.

The full global Cartesian product is not materialized. Sort the two lists. For each x in X, query Y in the cyclic interval

    [L-x, L+W-x) modulo M.

Split a wrapping interval into two ordinary half-open intervals. Each reported y produces r=(x+y) modulo M and the unique lift

    s = L + ((r-L) modulo M)

in I. No pair is duplicated, and no accepted integer is missed. A shift of each local set by -L gives the equivalent formulation seeking sums modulo M in [0,W). Membership checking alone, or an interval count alone, is not a substitute for the square test required by factoring.

Here is a conservative complete cost ledger. Let P be the largest selected prime and h cover the bit lengths of N, M, L, and L+W (plus a constant). Let G include prime generation, checking for small factors, constructing all local sets, building M, and finding all CRT inverses. Straight trial divisibility, square tables and extended Euclid give an elementary bound

    G = O((P² + sum_i ell_i + k) h³).

This intentionally loose bound makes preprocessing explicit. For the initial small primes with M=N^O(1), P=O(log M) by standard prime estimates, and G is polynomial in the input length. For arbitrary large chosen primes, G must not be treated as automatically polynomial in log M.

List construction takes at most O(k(A+B)) modular additions using staged products. Comparison sorting takes O((A+B) log(A+B+1)) comparisons of O(h)-bit values. Binary interval searches take O(A log(B+1)) comparisons in a random-access implementation. One can instead use sorted lists and monotone range boundaries, with sequential scans charging repeated emissions to K; this avoids assuming free random access on a finite-tape machine. Reporting and integer-square/factor validation cost O(K h³) using conservative elementary arithmetic. Thus a valid bit-cost upper bound, allowing the sequential implementation, is

    O(G + [k(A+B) + (A+B) log(A+B+1) + K] h³).

The stored lists take O((A+B)h) bits, in addition to local tables and polynomial arithmetic workspace. Output can be streamed. Even if only one factor is wanted, list construction is paid before the first query result. A favorable early square cannot retroactively erase preprocessing.

Assigning successive local sets to the group with smaller product keeps A/B between 1/d_max and d_max, where d_max=max_i |R_ell_i|. Hence

    2sqrt(D) <= A+B <= 2sqrt(D*d_max).

For small primes d_max=M^o(1), this is M^(1/2+o(1)) list work, rather than M^(1-o(1)) full-product work. It is a genuine bypass of full materialization **when K is small enough**. The missing factoring claim is an adequate bound on total work, including K, at parameters covering an unknown useful sum.

I checked an in-memory implementation against direct interval filtering. The edge grid used N in {1,9,25,49,10403,1022117}, the first k surviving primes from {3,5,7,11,13,17} for k=1,2,3,4, starts {-M-1,0,M-1,2M+3}, and distinct widths {0,1,min(17,M),M}. All **344** queries agreed, including empty/full intervals, wraparound, negative starts, squares, and singleton local sets. An additional **18** queries used the two original N values, k in {4,6,8}, L=ceil(2sqrt(N)), and W in {64,256,1024}. All agreed without any factors or corpus-family labels supplied to the query.

For a reproducible illustration at W=1024, greedy grouping by descending local cardinality produced:

    N=10403:   k=4: (A,B,K)=(5,8,35)
               k=6: (A,B,K)=(36,70,9)
               k=8: (A,B,K)=(385,648,1)
    N=1022117: k=4: (A,B,K)=(5,6,27)
               k=6: (A,B,K)=(54,30,10)
               k=8: (A,B,K)=(330,486,3)

Here M is respectively 1155, 255255, and 111546435. These K values include odd sums to match the original odd-prime diagnostic; filtering parity leaves 18,5,1 and 13,7,2. At k=8 the staged list constructions created 1920 and 1556 intermediate items respectively, before sorting and querying. These observations demonstrate the paid tradeoff: fewer survivors can accompany substantially larger lists. They establish correctness on finite cases, not scaling or a factoring speedup. The parent should not promote these extra, exploratory checks into preregistered performance evidence.

**Comparison with the paper and an appropriate baseline.** Hittmeir's Lemmas 3.4 and 3.6 cover the local and CRT counts; Algorithm 2.1 and Remark 4.5 permit streaming. Sections 5–6 formulate the multiple-choice subset-sum route. Algorithm 6.1 and Proposition 6.2 already give the two-list query with cost soft-O(A+B+K). Equation (5.1) supplies a heuristic short-interval survivor estimate; Remark 6.4 explicitly leaves the corresponding asymptotic improvement unproved. Section 5's isolation/minimum argument assumes a unique survivor; it cannot supply an unconditional useful-sum oracle. Theorem 4.6 gives a rigorous Fermat improvement of soft-O(Lambda exp(-((log 2)+o(1)) log Lambda/log log Lambda)), where Lambda is the minimum squared divisor gap divided by 4sqrt(N), not the raw gap. These are prior results, not H003 novelty. [Hittmeir, arXiv:2205.10074v1, §§3–6](https://arxiv.org/html/2205.10074v1).

Independently of any distribution heuristic, the group-count lower bound shows why the two-list method is not an automatically disruptive solver. If M grows as a fixed power of W, then k=O(log W/log log W). Even granting an idealized density estimate K approximately W/2^k would give K=W^(1-o(1)), not W^(1-epsilon) for fixed epsilon. That estimate is not a theorem for the actual N-dependent interval, and is not used to assert a lower bound there. Conversely, taking k proportional to log W in an attempt to get a fixed-power density reduction forces

    log M = Omega(log W * log log W),
    A+B >= 2sqrt(D) = exp(Omega(log W * log log W)).

For this explicit two-list implementation, that preprocessing is larger than every fixed power of W. Compact local input does not make the lists cheap.

There is also an exact, limited obstruction to a uniform reporting guarantee. For fixed N,M, let K_t count accepted residues in the cyclic interval starting at t of length W. Every one of the D residues belongs to exactly W such intervals, so

    (1/M) sum_{t=0}^{M-1} K_t = W*D/M.

Thus some interval has at least W/3^k outputs. When M is polynomial in W this is W^(1-o(1)). For larger M the two-list preprocessing itself eventually exceeds a proposed W^(1-epsilon) budget. Therefore one fixed pair of these lists cannot guarantee a fixed-power saving for reporting every translated interval. This averaging identity is deterministic; it is **not** an independence model, a statement about L=ceil(2sqrt(N)), or an obstruction to a method that chooses different constraints per interval or selectively extracts a square.

The direct local baseline for a publicly specified window is Fermat's scan: at most about W/2 square tests, each of polynomial bit cost. If N=pq with p,q within fixed unequal ratios of sqrt(N), then

    p+q-2sqrt(N) = (p-q)² / (p+q+2sqrt(N)) = Theta(sqrt(N)).

Such balanced inputs need not have close factors. A sieve argument leaving W^(1-o(1)) candidate work therefore provides no general improvement over exponent 1/2 in this sum search. Very close factors yield a smaller W and a special-family comparison only. In the general-input contract, neither a favorable factor gap nor a promised balanced interval is supplied. One may double W from a public starting value; its unsuccessful queries, rebuilding and validation all count. After treating even inputs, the public upper bound floor(N/3)+3 for a nontrivial positive factor sum covers odd composites, but is not a fast algorithm.

For a rigorous general factoring comparison, the already-established Harvey–Hittmeir bound is O(N^(1/5) (log N)^(16/5)/(log log N)^(3/5)) bit operations. It suffices to show how far a merely faster Fermat scan is from an appropriate general baseline; this review does not assert that it is the latest possible bound in every input class. [Harvey–Hittmeir, Theorem 1.1](https://arxiv.org/html/2105.11105). No NFS comparison or practical RSA advantage follows from these tiny diagnostics.

There is a particularly decisive comparison that needs **no** bound on K. This two-list query chooses M>=W. Therefore, on the balanced but non-close regime W=Theta(sqrt(N)), its compulsory preprocessing satisfies

    A+B >= 2sqrt(D) >= M^(1/2-o(1)) >= W^(1/2-o(1))
        = N^(1/4-o(1)).

It already loses to the established general exponent 1/5 before processing even one survivor. The statement is about constructing these explicit lists for the covering window, including a doubling schedule's eventual covering query. It does not rule out smaller close-factor windows, other ways to organize multiple queries, implicit lists, or algorithms that recover a factor without constructing them.

**Disposition and reopening gate.** Close H003's explicit-set gate as mathematically supported, with the qualifications above. Retain the two-list interval join as an exact known reference primitive if a future candidate needs one. Do not launch a further performance project for it under a claim of disruptive novelty: the examined algorithm is already prior art, its full cost is A+B+K up to polynomial bit factors, and the only proposed way to make K small enough either imports an unjustified short-interval assumption or makes its explicit lists enormous.

The decisive next requirement is a different, executable query that avoids the charged bottleneck, together with a parameter calculation proving its coverage and complete cost before benchmarking. For a general exponent improvement, it must in particular escape the N^(1/4-o(1)) list-construction barrier just identified. Merely counting local survivors, minimizing an assumed unique local solution, returning the first residue, or invoking an MCSS/LLL oracle does not meet that requirement. A route that selectively obtains a true integer-square discriminant must explain how it distinguishes that witness without inspecting all surviving candidates, price that operation, and retain completeness or a stated per-input success guarantee using N alone. No such costed new primitive emerged from this bounded review. This is a justified rejection of this proposed research continuation, not a lower bound against finding one.
