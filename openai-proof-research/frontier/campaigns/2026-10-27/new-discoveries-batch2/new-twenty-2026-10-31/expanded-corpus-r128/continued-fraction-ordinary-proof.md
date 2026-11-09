# 371294: ordinary proof route, not a Lean certificate or an acceptance

Target: Singh–Zhang–Hildebrand, arXiv:2511.01992v1, Conjecture 6 (and Conjecture 4). The author-hosted INTEGERS version was retrieved separately. The source's Lemma 2.5 and Lemma 5.2 reduce equality of Gauss–Kuzmin measures of equal-length words to equality of their characteristic numbers. This note supplies a uniform polynomial nonidentity argument. Root must decide substantive eligibility: the bridge from the source's formula to a classical polynomial zero estimate is short. No prior full endpoint is asserted absent from the literature, and no formalized solution is claimed.

Let n >= 4, and let x_1,...,x_n be independent commuting indeterminates. For an ordering w=(w_1,...,w_n) of these distinct variables write K(w) for its continuant, K(empty)=1, K(x)=x, and K(w_1,...,w_j)=w_j K(w_1,...,w_{j-1})+K(w_1,...,w_{j-2}). Set Q=K(w), P=K(w_2,...,w_n), R=K(w_1,...,w_{n-1}). The source's characteristic polynomial is C_w=(Q+P)(Q+R), of total degree 2n. Indeed the matrix product of [[0,1],[1,w_i]] has bottom right Q, top right P, bottom left R.

Write X=product_i x_i. The terms of Q in degrees n and n-2 are respectively X and sum_{i=1}^{n-1} X/(w_i w_{i+1}); all remaining terms have degree at most n-4. This follows by induction from the continuant recurrence, or by the matching expansion of the path. Similarly, P has leading term X/w_1 and remaining degrees at most n-3; R has leading term X/w_n and remaining degrees at most n-3. Therefore the homogeneous parts of C_w in its top three degrees are:

* degree 2n: X^2;
* degree 2n-1: X^2/w_1 + X^2/w_n;
* degree 2n-2: 2 sum_{i=1}^{n-1} X^2/(w_i w_{i+1}) + X^2/(w_1 w_n).

These are monomials in a polynomial ring; the division notation only abbreviates cancellation of factors of X^2. Since n >= 3, the endpoint pair is not an edge of the path. The degree 2n-1 part recovers the unordered endpoint pair. After subtracting the endpoint-pair monomial, the degree 2n-2 part recovers exactly the unordered adjacency pairs of the ordering. A finite path graph determines its vertex order up to reversal: starting at either endpoint, at every step the only unused neighbour determines the next vertex. Consequently C_w=C_v as polynomials if and only if v=w or v is the reversal of w.

For completeness, if a nonzero polynomial F in n variables over Q has total degree d, then it has at most d N^(n-1) zeros in {1,...,N}^n. Induct on n. Regard F as a degree e polynomial in its last variable, with nonzero leading coefficient G of degree at most d-e in the first n-1 variables. There are at most (d-e)N^(n-2) assignments where G vanishes; allow all N last coordinates there. At every remaining assignment there are at most e roots. The total is at most (d-e)N^(n-1)+eN^(n-1). The n=1 base is the elementary univariate root bound.

For every pair of orderings sigma,tau not related by reversal, C_sigma-C_tau is a nonzero polynomial of degree at most 2n. An unordered n-tuple of distinct integers counted by f(N,n) gives at least one such pair having equal characteristic number, by the source's definition and Lemma 5.2. A union bound over at most (n!)^2 pairs bounds f(N,n) by 2n(n!)^2 N^(n-1), since each increasing tuple injects into the grid and a collision for that tuple is covered by the union. Thus

  delta(N,n) <= 2n(n!)^2 N^(n-1) / binomial(N,n) -> 0.

For instance, for N >= 2n, binomial(N,n) >= (N/2)^n/n!, giving delta(N,n) <= 2n 2^n (n!)^3/N. This resolves the ordinary asymptotic assertion; it does not establish the much sharper conjectured exponent of f(N,n).

The same zero-set union bounds all ordered words with nontrivial symmetries, without requiring distinct digits: a nontrivial numerical permutation still corresponds to two index orderings not equal or reversed, and the same polynomial union includes its assignment. Hence Conjecture 4 follows directly as well, even without separately disposing of the O(N^(n-1)) repeated-digit words.

Diagnostics: scripts/continued.py independently expands these polynomials for 3 <= n <= 10 and verifies every coefficient used above. It also exhausts distinct digit subsets for (n,N)=(4,25),(5,15),(6,12),(7,10),(8,9). These diagnostics are not formal proofs. The source's exact finite tables extend to N=120,60,35 for n=4,5,6, so these first three sweeps do not exceed the source's coverage. The n=7,8 sweeps are new parameter coverage only and have zero separate credit.

Remaining formal work is substantial: exact continued-fraction/measure semantics, the continuant matrix bridge, coefficient recovery under arbitrary variable permutations, the finite grid zero estimate and the density limit must all be formalized. A theorem about arbitrary polynomials alone would be a surrogate. No Lean packet has been created.
