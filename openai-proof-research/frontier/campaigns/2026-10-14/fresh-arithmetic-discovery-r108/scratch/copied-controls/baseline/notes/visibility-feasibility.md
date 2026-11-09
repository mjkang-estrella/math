# Primitive lattice-point square gaps: prefreeze calculations

Status: PREFREEZE / no nominee. This is an investigation of an existing sharp-order question, not a frozen or newly claimed theorem. The deductions below are author calculations; the CRT and prime-product operations are classical and do not establish a substantial new result. Source021 and all its operative proof operations at the stipulated pin are accepted as true throughout.

## Working question and exact quantifiers

Does there exist an absolute C and x0 such that, for every integer x >= x0 and every integer y >= x, the square

    {(x+i,y+j): 0 <= i,j < ceil(C sqrt(log x / log log x))}

contains a pair of coprime coordinates? There is no upper bound on y. Define a square to be hidden if every displayed gcd exceeds 1. Erdős's 1958 paper supplies the classical logarithmic upper scale and square-root logarithmic lower scale. Nothing in this file resolves their gap. The paired-Jacobsthal quartic target in arithmetic r1 is a different immutable scope, not a nominee here.

## Exact row-capacity reduction

Fix positive x and integer L >= 2. For each small prime p <= L dividing at least one x+i, choose b_p modulo p. Set

    R_i(b) = {j in [0,L): b_p+j != 0 mod p for every p <= L dividing x+i},
    k_i = #{distinct prime divisors p > L of x+i}.

There exists y >= x producing a hidden L by L square if and only if some choice b satisfies |R_i(b)| <= k_i for every row i.

Necessity: take b_p = y mod p. A remaining cell must be covered by a prime > L dividing both coordinates. Such a prime covers at most one column, since distinct column offsets differ by less than L. Different remaining columns in a row therefore require different large primes.

Sufficiency: assign distinct large divisors of x+i to the columns in R_i. A prime > L cannot divide two different row coordinates, since it would divide a nonzero difference of absolute value less than L. All assigned large primes are thus globally distinct. Impose y = -j mod p at each assigned prime, and y = b_p mod p at the small primes. CRT gives an entire progression of solutions, including arbitrarily large positive y >= x. All other cells already have a chosen small-prime divisor. The case x+i=1 gives k_i=0 and R_i all columns, correctly precluding hiding.

This equivalence removes the unbounded y coordinate exactly. Its necessity and sufficiency are elementary CRT; they are not a new contribution claim. It identifies the unproved obligation: exclude the simultaneous capacity inequalities for every x at the proposed square-root scale, uniformly in the small-prime choices.

## Uniform small-prime residual density

For arbitrary pairs (a_p,b_p) mod p, p <= L, let T_L count (i,j) in [0,L)^2 outside every point congruence (i,j)=(a_p,b_p) mod p. Then

    T_L = (1/zeta(2) + o(1)) L^2,

uniformly in all the residue choices. Here is a proof with no unjustified uniform fundamental-lemma input. Fix w. CRT counting for primes <= w with fixed period W gives delta_w L^2 + O_w(L+1), where delta_w = product_{p<=w}(1-1/p^2). The further deletion for w<p<=L is at most

    sum_{w<p<=L}(L/p+1)^2
      <= L^2 sum_{p>w}p^-2 + 2L sum_{p<=L}p^-1 + pi(L).

The latter two terms are o(L^2), and the first has arbitrarily small coefficient as w increases. The fixed-w count is also an upper bound for T_L. First send L to infinity and then w to infinity. This proves the assertion uniformly; it does not assert an error bound with an arbitrarily growing w.

Apply this with a_p=-x and b_p=-y. Any hidden square needs m >= (delta+o(1))L^2 distinct large primes, delta=1/zeta(2). They all divide P=product_{i<L}(x+i). Distinct positive integers already give product >= m!, so Stirling (or an elementary sum of logarithms) yields

    L log(x+L) >= log P >= log(m!)
                    >= (2 delta + o(1)) L^2 log L.

Consequently log(x+L) >= (2 delta+o(1))L log L. This recovers a classical logarithmic-scale upper bound. The constant zeta(2)/2 appears among the refinements already discussed by Erdős; it is not claimed as an improvement. His paper also states a stronger elementary constant. No sharp-constant claim is made here.

The desired square-root scale instead requires an obstruction at roughly log x >= c L^2 log L for hidden squares. The product argument loses an entire factor L because its upper bound is x^L, not x. Replacing that upper bound by x would be false.

## What the CRT construction does and does not show

Conversely fix w and impose x=y=0 mod all p<=w. In the L by L offset grid, m=delta_w L^2+O_w(L+1) cells remain. Assign one distinct prime > max(w,L) to each such cell, and impose x=-i, y=-j modulo its prime. CRT yields positive representatives <= M in each coordinate, M the product of all imposed primes. Their order can be interchanged to ensure y>=x. Selecting the first m available primes gives log M=(2 delta_w+o(1))L^2 log L by the prime number theorem. This is the familiar prime-matrix construction, with small primes reused. It explains the square-root scale but supplies an upper bound on the constructed coordinates, not a lower bound for all hidden coordinates. This construction and its refinements belong to the classical/hidden-forest antecedents; no nominee is based on it.

The least positive solution of many congruences can be far below their modulus. For instance, x=14,L=2 has row primes 7 and 3,5, with total modulus 105 > x. More generally the actual coordinate is already a small common CRT solution to its row-prime constraints. There is no general lower-bound reversal of CRT.

## Direct use of Source021 and the inverse-sieve operations

On the diagonal, gcd(x+t,y+t)=gcd(x+t,y-x). The source bound h(k) << k^2/(log log(3k))^2 gives a diagonal interval depending on omega(y-x); this is uncontrolled when y is unrestricted. Applying it to one row uses k=omega(x+i) and does not approach the proposed square-root scale. Its global bound in terms of this k is too long even compared with the classical logarithmic square bound.

The exact least-bad-prime partition is available in dimension two. But the reference density of a point congruence is 1/p^2, not 1/p. For squarefree d, a fixed congruence point has count

    L^2/d^2 + O(L/d+1).

For d>L the actual count is zero or one and the reference is tiny. The many primes covering the residual cells lie precisely in this range. Summing their boundary errors loses the whole residual mass. The convergent small-prime product is already handled by the preceding uniform density calculation; a new argument is needed for the large-prime locations.

Source021's inverse proposition uses a dense, independently varying (p,q,u) box and many discrepancies N_pqu - N_pq/u. It produces a finite whole-box list of small rational intercepts through incidence counting, polynomial interpolation, nonlinear-curve control and rational-line extraction. A hidden square by itself assigns different primes to different cells. It has not supplied that incidence hypothesis, nor a long critical progression with the required independent choices. Walsh's actual characteristic-set proof likewise needs many simultaneous congruence incidences for each typical point. Covering distinct cells once with different primes is not that premise.

There is also a real structured alternative: all row congruences already have the rational intercept -x. Obtaining a rational explanation for them is compatible with the original hidden square. Its height is not automatically in the source's stopping window. A conclusion that the configuration is algebraic therefore does not yet exclude it.

## Low-degree polynomial compression attempt

Let M_i be the product of the selected distinct large row primes, M=product M_i. They are pairwise coprime across rows and x=-i mod M_i. For every integer polynomial F,

    [M_i divides F(-i) for every i]  iff  M divides F(x).

The forward direction evaluates modulo each M_i; the reverse uses the same congruence. A pigeonhole/Siegel construction of a polynomial with small coefficients satisfying the row congruences is thus only constructing a polynomial relation at the single CRT value x modulo M. It can yield the actual linear polynomial F(T)=T-x whenever its allowed coefficient height reaches x. Forcing F(x)=0 is then a consistent conclusion, not a contradiction. The degree-L polynomial product_{i<L}(T+i) accounts for all prime divisibility and recovers the product bound. To improve the height scale one must either force more than deg(F) distinct genuine roots, or control the resulting rational intercept in a way that also defeats the simultaneous column capacities. Neither has been established.

This identifies why a purely formal composition of CRT, source inverse extraction, and polynomial interpolation is insufficient. It does not prove that every stronger integrated argument fails.

## Outstanding task

Continue reading the operative source stopping comparison and the actual hidden-forest constructions, then test whether they give the missing uniform small-coordinate obstruction. No frozen scope, full proof, correctness grade, contribution grade, or campaign-count assertion follows from the deductions above.

## Completed stopping comparison and a stronger integrated attempt

Read the full Source021 stops.tex after the initial calculations, including lem:stops-aligned-average, prop:stopped-comparison, and prop:hard-stopping. These are stipulated available operations. The aligned average writes Dn-A=pq'm, restricts m to +/-d0*l with d0 small and l prime, and sieves the independently varying tag prime p. Its common m-interval and Siegel--Walfisz ranges use D<=w^Cs and |A|<=Y*w^(Cs+2), J_p between P^2.03 and P^2.19, and an entire large prime subbin. The comparison survives deleting a small nonaligning fraction by an absolute individual upper bound. The hard-endpoint proof creates near-full bins from independent full-box choices before conditioning and uses a marked even path visit. Thus there is an actual compatible positive completion in the scalar source; it is not an unexplained source gap.

Try to use these operations more strongly as follows. Translate the fixed row interval by x. Every assigned prime p>L has a unique row label i_p in [0,L), and its forbidden scalar class is i_p, which is already small. Distinct row labels define distinct rational intercepts i. If an inverse argument could concentrate a positive fraction of all m~L^2 assigned primes on a bounded number of rational intercepts, one row would carry >>L^2 primes, giving log x >> L^2 log L and closing the working scale. However, the exact row-capacity inequalities allow the primes to be spread across all L labels. Pigeonhole gives only m/L~L primes per label, precisely the classical bound. Source021 does not state a bounded-intercept conclusion for an arbitrary short interval with arbitrary many forbidden primes. Its bounded-list inverse conclusion is for the independently populated discrepancy boxes at its own scalar critical scale. Here k~L^2 and interval length L, whereas the cardinality theorem has interval length of order k^2, about L^4 up to logarithms. Applying it literally supplies no such concentration.

The stopping average does not fix this mismatch. Replacing a tag prime in a bin changes the condition that it divide the fixed number x+i. Restricting replacement to actual divisors can leave a very sparse subset of the bin, not the 1-eta fraction required by the owner argument. Alternatively allowing all primes creates hypothetical row patterns that need not occur at the fixed x. A lower average over those hypothetical patterns is not a lower bound at the original x. Thus the rational extraction and the positive completion have both been considered together, with their actual averaging hypotheses, rather than rejecting them merely because a factorized estimator fails.

## Averaging over x does not prove the uniform assertion

The exact capacity reduction also suggests counting exceptional x in [X,2X]. A hidden square forces sum_{i<L}omega_{>L}(x+i) >= (delta+o(1))L^2. Elementary averaging bounds the expectation by O(L log log X + L*pi(3X)/X) for L<=X, by counting multiples of each prime. For L much larger than log log X this already gives a vanishing proportion via Markov. This is a statement about almost all x, not every x. Higher divisibility moments count solutions of congruences modulo products M. The standard X/M+O(1) count gives useful independence when M is below X; when many selected row primes have product far above X, the O(1) term is exactly the possible exceptional small CRT solution. Dropping it would assume the missing conclusion. No average statement or restricted-height result is substituted for the full question.

## Final mathematical disposition

No full result closes. The exact unproved obligation is to show that, for some absolute C and every sufficiently large x, setting L=ceil(C sqrt(log x/log log x)) makes the simultaneous row-capacity inequalities impossible for every small-prime residue assignment. The strongest integrated route investigated combines exact CRT capacities, uniform residual density, distinct-prime product growth, low-degree interpolation, the source's whole-box rational extraction and its aligned positive stopping average. The first three give the classical logarithmic scale; interpolation admits the existing coordinate as a root; the last two lack the necessary independent whole-bin ensemble at the working scale. This is not an impossibility result for these methods, an exhaustion claim, or a literature-priority claim. All supporting proved deductions are classical compositions. There is no candidate theorem to freeze and no independent TECHNICAL grade is assigned.
