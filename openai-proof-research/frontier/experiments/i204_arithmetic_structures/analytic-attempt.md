# I204 analytic attempt — final record

Completed screening of 025 (short Egyptian fractions), 027 (integral character varieties), and 028 (Gaussian-prime components). Source truths are stipulated. The final outcome is NO VIABLE TARGET IN THIS ROUND. The early entries below record the elimination sequence; subsequent sections contain the completed proofs, limits and gaps. No computational experiments were run.

## Early elimination: near-linear denominator cap

Let p be prime, let `(p-1)/p = sum_{i=1}^k 1/n_i`, and suppose `N=max n_i<p^2`. Write `n_i=p m_i` for the s denominators divisible by p and put `M=floor(N/p)<p`, `L=lcm(m_1,...,m_s)`. Denominators not divisible by p are p-adic units. Multiplying the equality by p and reducing modulo p gives `-1 = sum_i m_i^{-1} (mod p)`. Hence the positive integer `L+sum_i L/m_i` is divisible by p. In particular

`p <= (s+1)L <= (s+1)M^s <= (k+1)M^k`.

This is a proved elementary obstruction, not a nomination. For `N<=p(log p)^A` it forces `k >= (1/A-o(1)) log p/loglog p` (fixed A>0). Consequently a simultaneous near-linear cap and `O(loglog p)` length is impossible. No numerical scan was used.

The full 1990 Tenenbaum–Yokota paper explicitly attributes a stronger simultaneous lower obstruction to Yokota 1986 (p.151, equation (4)) and says the coefficient one in its near-linear-cap length theorem is optimal. The displayed simple p-adic bound is therefore not treated as new prior art or as a substantial contribution. The full 1986 article was not read; its primary abstract/metadata were consulted, and the lower-obstruction attribution is used only as reported in the primary 1990 paper.

## Selected target to test

A polynomial cap remains a meaningful separate question: do there exist absolute A,C,b0 such that every integer b>=b0 and 1<=a<b has a distinct expansion with `k<=C loglog b` and `max n_i<=b^A`? This is a candidate, not a proved or asserted-open result. Two routes were selected: control the full denominator cost of the source residue descent, and construct short divisor sums in one polynomial-sized common denominator. Merely extracting a stretched-logarithmic cap from source length is explicitly below the contribution gate.

## Route A: an obstruction to polynomial cost in the literal residue recursion

This is a method limitation, not a negative answer to the polynomial-cap target. Fix the source constants `A=D_M`, `L=D_C`, `B=2D_C`, `H=D_X`, so `L>H>1`. For `S` large let

`exp(S)<M<=exp(A S)`, `exp(L S)<=C<=exp(B S)`, `X=exp(H S)`.

Allow **all** positive divisors of M, not merely the source's selected lists. A high-stage transition from an integer `1<=u<=X` chooses `t|M` and sets

`z=ceil(Ct/u)`, `h=uz-Ct`, `0<=h<u`.

Stop on first reaching `h<=exp(S)` (including h=0). There exist constants `theta,gamma,c>0`, depending only on A,B,L,H, such that all but at most `X exp(-gamma S)` starting integers u in `[1,X]` require more than `floor(theta log S)` high transitions before stopping. Every literal recursive expansion along such a path emits a denominator at least `exp(c S log S)` before the high stage finishes.

Proof. For any fixed K0 and `n<=exp(K0 S)`, factor n at `sqrt(S)`. Small primes contribute at most `sqrt(S) log(1+K0 S/log 2)=o(S/log S)` to `log tau(n)`. The total multiplicity of primes greater than `sqrt(S)` is at most `2K0 S/log S`; use `a+1<=2^a` on their exponents. Thus, uniformly,

`tau(n)<=exp(K1 S/log S)`, with `K1=2K0 log 2+1`

for sufficiently large S. Take `K0=A+B+H+1`. For a specified h and divisor t, any predecessor u divides the positive integer `Ct+h<=exp(K0 S)`. Since there are at most `tau(M)` choices of t, the number of predecessors of h is at most

`R_S=exp(K S/log S)`, `K=2K1`.

Backward counting from the at most `floor(exp S)+1` terminal h's bounds all starting u that stop within J steps by

`(floor(exp S)+1)(J+1) R_S^J`.

Choose `theta=(H-1)/(4K)` and `J=floor(theta log S)`. Its logarithm is at most `(1+(H-1)/4)S+o(S)`, which is at most `(H-gamma)S` for `gamma=(H-1)/2` and all large S. This proves the exceptional-set estimate uniformly in M,C.

For a path not counted, the first J transitions stay in the high stage. Every `z_j>=C/X>=exp((L-H)S)`. Substituting the identities recursively gives the jth emitted denominator

`N_j=(M/t_j) z_j product_{i<j} z_i`.

Consequently `N_J>=exp((L-H)S J)>=exp(c S log S)` for `c=(L-H)theta/2` eventually. The source's later scaling by a positive integer only increases these raw denominators. Positivity rules out cancellation within the literal sum.

Validation and limits. Counting includes paths ending at zero, repeated choices, arbitrary divisors, and paths that jump many levels. It does not assume typical residues or random independence. K0 covers the upper range of Ct+h. Allowing repeated or distinct raw unit fractions changes neither argument. A subsequent algebraic *replacement* of the raw sum, including Takenouchi cleanup, is not covered: this lemma does not say every short representation has a large denominator, and it does not establish a lower bound for the optimal final cap. The source density set has at least `7X/8` elements, whereas the fast-stop set is exponentially negligible, so a polynomial cap cannot be obtained simply by selecting fast paths for every member of that same dense family. A different dense-family construction or a new bounded-size replacement operation would be needed.

## Route B: one common denominator, and where the sparse-divisor approach fails

A sufficient construction for the target would give, for every b, an integer `Q=bM<=b^A` such that every `aM` (`1<=a<b`) is a sum of `O(loglog b)` distinct positive divisors of Q. Dividing by Q would give the required unit fractions. This is stronger than the original target: arbitrary successful expansions need not share one polynomial-sized Q. The source's final density argument and its literal recursion do not supply this property.

### Binary reservoir cannot work

Fix real constants `A>1,C>0`. Let p tend to infinity through odd primes. Consider every integer t with `0<=t<=(A-1)log_2 p`, and all distinct unit-fraction sums with at most `k=floor(C loglog p)` terms whose denominators divide `Q=p 2^t`. There are only `2(t+1)=O_A(log p)` divisors of Q. For each t the number of subsets of at most k divisors is at most `(2(t+1)+1)^k` (encode the sorted subset padded by a blank symbol). A given subset represents at most one a/p. Even after taking the union over all allowed t, at most

`O_A(log p) [O_A(log p)]^{C loglog p} = exp(O_{A,C}((loglog p)^2)) = p^{o(1)}`

numerators a can occur. The fraction of all `p-1` numerators represented tends to zero. Allowing t to depend on a does not repair this obstruction. Thus a binary common denominator is inadequate even though it can make every rational attainable with a much longer expansion. This is a counting proof, not a numerical test.

### A subquadratic common denominator is impossible even without a length bound

Fix `epsilon in (0,1)`. For all sufficiently large primes p and integers `1<=M<=p^{1-epsilon}`, there is no distinct expansion of `(p-1)/p` all of whose denominators divide `pM`. Since `M<p`, every divisor of pM is either m or pm, with `m|M`. Multiplying the expansion by pM gives

`(p-1)M=pT+S0`,

where S0 is a sum of distinct divisors of M (from denominators pm), and T is another such sum. Thus `S0+M` is a positive multiple of p. But

`0<S0+M<=sigma(M)+M<=M(tau(M)+1)<p`

for all large p, by the elementary divisor bound proved above (or `tau(M)=M^{o(1)}`). Contradiction. The case M=1 is immediate. This excludes this **common-denominator** construction with exponent below 2; it does not exclude arbitrary expansions with maximum denominator below p squared. Their least common multiple can greatly exceed their largest denominator.

### Remaining unpaid step

A divisor-rich choice such as an integer built from small primes escapes the binary counting obstruction. However, its divisors must supply *short exact* positive subset sums for all the values aM, not merely many residues modulo b. A modular relation leaves a multiple of b to be corrected and may destroy positivity or the length bound. Tenenbaum–Yokota's dense-divisor construction pays roughly `log b/loglog b` terms in the hard correction stage. The source's rational-divisor supply changes the common denominator and then uses a greedy remainder; its scalar divisors do not already give the above simultaneous exact sparse-subset property. No proof of that property, or replacement that avoids it, was found here.

## Technical ceiling supplied by the accepted theorem alone

If `0<a/b<1` has a sorted k-term positive unit-fraction expansion, put `P_j=product_{i<=j} n_i`, `P_0=1`. The positive remainder before term j has denominator dividing `bP_{j-1}`, hence is at least `1/(bP_{j-1})`, and at most `k/n_j`. Therefore

`n_j<=kbP_{j-1}`, `P_j<=kbP_{j-1}^2`, `n_j<=(kb)^{2^{j-1}}`.

The accepted `k<=C0 loglog b` theorem consequently gives an absolute E and b0 such that every a/b has a distinct expansion of length at most `C0 loglog b` with largest denominator at most `exp((log b)^E)`. For example, any fixed `E>1+C0 log 2` works after increasing b0. This is a routine consequence of positivity and the source theorem, not a nomination or a polynomial cap. The coefficient C0 is not extracted or claimed explicit.

## Family 027: arithmetic restrictions screened

Read the complete manuscript build, including both figure sources, diagrams and full rank-reduction, surface, dynamics and descent arguments. Its fixed field and free integral representation construction already cover all components and exact complex boundary classes; taking another field extension or specializing the genus/rank supplies no missing mechanism.

A technical finite-congruence fact illustrates what is easy. For a nonzero ideal I in a number ring R, the principal congruence subgroup of `SL_r(R)` is Zariski dense in `SL_r(C)`, for r>=2: it contains each elementary transvection `1+t E_ij` for t in the infinite set I; its closure contains the full root subgroup; these generate `SL_r(C)`. Thus, for a free group F_d and any integral representation rho0, the tuples congruent to rho0 modulo I are Zariski dense in `SL_r(C)^d`, by translation and products. This does not prove the corresponding claim with a surface relation and fixed peripheral classes. The free-group deduction is routine and is not nominated.

The tempting strengthening is to preserve an exact nonsemisimple boundary stratum at every finite prime. The source only selects a complex open locus after taking the quotient. The implication “nonzero minor over C, hence the same minor has full rank at every finite prime” is false: `U(t)=[[1,t],[0,1]]` has rank(U(t)-1)=1 over C for t!=0, but U(2) becomes the identity in characteristic 2. Inverting that minor requires a unit condition, not just avoiding its complex zero locus. The integer 2 cannot become a unit in any finite extension's full ring of integers. This is a counterexample to that inference, not to existence of other integral points with prescribed reductions. No relative congruence-preserving rank induction was constructed, and no claim is made that the proposed stronger density statement is false.

Primary comparison: Coccia–Litt's surface theorem and dense mapping-class orbit already handle rank two with arbitrary integral traces. Their introductory statement and surface theorem/field remark were read directly. A word search for “congruence” is not a theorem about its absence. No new higher-rank strong-approximation assertion follows from this screen.

## Family 028: effectiveness screened

Read the complete finite-sieve manuscript build, including the rectangle lemma, shared-data coverage transfer, all scheduling quantifiers, posterior-mixture step and common-law entropy telescope. The accepted source already gives one finite sieve for every D and an explicit bound in terms of its modulus Q. Merely solving its “sufficiently large” inequalities for a huge D-dependent threshold is constant extraction, excluded by the contribution gate.

For a fixed finite set P of split primes, a fully elementary finite-graph certificate can be described. Form the graph on allowed residues modulo Q, with each edge labeled by the physical lattice displacement v of length at most D. Keep parallel labeled edges and loops (residue coincidence does not mean physical displacement zero). In each component choose a spanning tree and assign the sum of labels along tree paths as an integer-vector potential. A nontree edge has a cycle displacement, which lies in Q Z^2. All such displacements vanish if and only if every lifted component is finite: if they vanish, lifts are given by one potential per residue; if one is nonzero, repeated lifting of the closed walk gives an infinite connected component, hence an infinite simple path by local finiteness. In the finite case each lifted component has at most one vertex per allowed residue.

CRT counts those allowed residues as `V=product_{p in P}(p-1)^2`, giving the technical replacement of Q^2 by V in the source periodicity bound. The exceptional Gaussian primes number `8|P|`, so the same deletion/reattachment proof bounds a prime component by

`max{V, 8|P| [1+(K_D-1)V]}`.

This is a finite-graph reformulation and counting refinement of the source's existing periodicity operation; it is not a genuinely new effective sieve mechanism. In principle one can enumerate finite prime sets and test this certificate; the stipulated finite-sieve theorem assures eventual success. That supplies neither a new a priori complexity bound nor an analytic prime-selection estimate. No enumeration, graph construction, or test was run. The exact unpaid quantitative input would bound the first successful prime set directly in terms of D by a mechanism beyond tracing the source's thresholds.

## Disposition

NO VIABLE TARGET IN THIS ROUND. The polynomial denominator-cap statement is unresolved here, with two distinct failed routes and proven limitations. The other families offer only routine consequences or an unpaid arithmetic/quantitative bridge. None of the partials is proposed as the ninth substantial finding. Both independent acceptance gates remain with the parent.
