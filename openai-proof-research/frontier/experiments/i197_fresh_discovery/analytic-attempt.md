# I197: two analytic routes and the contribution boundary

Completed 2026-10-12. **Technical deduction, not a nomination.** All OpenAI theorems and lower proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. Nothing below audits their truth. The initial PARTIAL stub is superseded by this complete argument and its explicit remaining gap.

## 1. Source contracts actually used

Write `P(a)=1` when `a` is prime and zero otherwise, `theta(a)=log(a)P(a)`, `L=log X`, and `E_X=X^{-1} sum_{X<m<=2X}`. In the pinned 026 manuscript:

* `thm:main` gives positive ordinary lower index density of `p_{n+1}-p_n>C log p_n` for each fixed C. `cor:ratios` is already the ratio-increase consequence.
* `prop:mixed-moments` evaluates a fixed product of smooth divisor sums with arbitrary fixed equality pattern, uniformly for shifts of size `O(L^B)`. The total support budget is `<1` without a prime mark, `<1/2` with **one** prime mark. Its error is additive `L^{-t} O(L^{-1/2}(log L)^A)`. Only the one marked shift is allowed to carry theta.
* `lem:singular-average` averages the singular series over distinct shifts in fixed boxes of equal side length h, in a containing interval of diameter at most Kh. K and the number of coordinates are fixed. Its zero-safe proof does not assume admissibility of every tuple.
* `prop:weight-moments`, `eq:prime-deletion`, and `prop:dimension-cancellation` yield the quadratic forms

  `w=sum_j lambda^j/j! ||f_j||_2^2`,

  `v=lambda sum_j lambda^j/j! ||f_j+T f_{j+1}||_2^2`,

  with `w>0`, `v/w` arbitrarily small, `E Z^4=O(1)`, and an external prime detector bounded independently of the chosen suppressing family. Here `T f(t)=integral f(t,u)du`.

The functions have support in a simplex of radius `tau=1/8`. A fixed smooth one-dimensional majorant G has `G(0)=1`, vanishes for `u>=tau`, and

`c_G=integral_0^infinity |G'(u)|^2 du`, `c=c_G^2`.

At a prime argument larger than X, `D_G(m;b)=1`; thus `P(m+b)<=D_G(m;b)^2`. This is an **upper**, not a lower, prime detector. The source budgets used below are `2tau<1/2` (one mark), `4tau<1` (fourth moment), and `6tau<1` (two majorants plus the square).

All eight 026 source files are retained and hash-bound in the authentication record. The full five sections, not just their statements, were read.

## 2. Route A: many small detector windows, with a first/second-moment score

### 2.1 Exact technical statement

For every real C>0 and integer ell>=1 there exist finite constants

`B=B(C,ell)>C`, `eta=eta(C,ell)>0`, and `N_0=N_0(C,ell)`

such that every integer N>=N_0 satisfies

`#{1<=n<=N-ell : C log p_{n+j}<p_{n+j+1}-p_{n+j}<=B log p_{n+j} for all 0<=j<ell} >= eta N`.

Thus the ell gaps really are consecutive, and the chain ends by p_N. B is chosen by the proof; it is not a prescribed endpoint near C. All parameters are fixed before X tends to infinity. No uniformity for growing C, ell or N-dependent choices is asserted.

This statement is stronger than simply intersecting ell positive-density sets, an invalid inference. Its proof uses the lower operations of 026. Its contribution status is assessed in section 5.

### 2.2 The finite-union version of the accepted weight operations

Fix positive delta and finitely many disjoint cells, each of h=floor(delta L) consecutive shifts, all in a strip of O(h) shifts with fixed implicit constant. Let S be a nonempty union of selected cells to be suppressed, and let D be a disjoint union of detector cells. Suppose S has s cells and D has k cells. Put `lambda=s delta`, `H=k delta`.

Use exactly the source square, now summing its subsets over S:

`Z(m)=sum_{j=0}^d sum_{A subset S, |A|=j} D_{F_j}(m;A)`.

The maximum divisor dimension d is unrelated to k, the number of detector cells. For every epsilon>0, the source cancellation construction at parameter lambda provides a single finite family with `w>0`, `v/w<=epsilon`. Freeze it and put `W=Z^2/w`.

The source proofs give, with `N_E(m)=sum_{b in E}P(m+b)`,

(1) `E_X W -> 1`, `limsup E_X(W N_S)<=epsilon`, `E_X W^2<=M` for all sufficiently large X, for a finite M;

(2) `E_X(W N_D)->H`;

(3) `limsup E_X(W N_D^2)<=H+c H^2`;

(4) for each detector cell D_i, `limsup E_X[W binom(N_{D_i},2)] <= (c/2) delta^2`.

Here c does not depend on epsilon or on the suppressing functions. M can depend on all of them. These assertions require a proof of the changed shift geometry, not an invocation of the headline theorem:

1. Expand each shift sum into its finitely many cell assignments. For each equality pattern, distinct numerical shifts range over a box of side h. The source singular-series lemma applies with the same fixed containing-diameter constant, even when several coordinates use the same cell. Summing these finitely many box means gives the appropriate products of the cell counts. In particular `binom(|S|,j)/L^j -> lambda^j/j!`. There is no loss from inadmissible tuples: zero singular series are included in the source's additive estimate and its average.
2. Unmatched coordinates from the two copies of Z still put an f_j coordinate on a vanishing face. Only matching subsets survive. Consequently E Z^2 and E Z^4 have exactly the source limit and boundedness, and a mark external to S gives `E(W N_D)->|D|/L -> H`.
3. For a mark inside S, delete that marked shift exactly as in `eq:prime-deletion`. The identity changes f_j to `f_j+Tf_{j+1}`; it does not depend on the marked cell or create an extra j factor. The total marked form is therefore still v, and (1) follows.
4. For two distinct external shifts b,c, replace `P(m+b)P(m+c)` by `D_G(m;b)^2 D_G(m;c)^2`. The accepted six-factor unmarked formula and face vanishing leave only matching subsets from Z. The coefficient is `c_G^2 ||f_j||_2^2`. Averaging ordered b,c over D gives `c H^2`; averaging over D_i gives `c delta^2`. Adding the exact diagonal `N_D` proves (3). Dividing the within-cell ordered-pair count by two proves (4).
5. The source marked formula uses theta/L, but on the whole fixed strip it equals `P(1+O(1/L))`, uniformly. Nonnegativity and the bounded marked means justify replacing it by P in (1)-(2); the limiting constants are unchanged.

Only finitely many patterns occur after the family has been frozen. For a pattern with t distinct unmarked shifts, there are O(L^t) assignments; the additive error is `L^{-t}o(1)`. An extra external mark supplies one more sum and the factor 1/L. Thus all total errors are o(1). No assertion uniform in d, k or epsilon as these vary with X is used.

### 2.3 Choosing the geometry and the score

Put `r=ell+1>=2` and `H=2r`. Choose an integer k so large that

`delta=H/k <= 1/[2c(r+1)]`.

Choose an integer q>=1 with `q delta>C`. Make k detector cells D_1,...,D_k, each of length h=floor(delta L), with q consecutive suppressed cells between each adjacent pair. There are no uncovered shifts inside the strip. Its length is

`T_X=[k+(k-1)q]h <= A L`, where `A=[k+(k-1)q]delta`.

Now S has `(k-1)q` cells and source parameter `lambda=(k-1)q delta`. Fix `epsilon=1/(4r)` and construct W as in section 2.2. Set

`n_i=N_{D_i}`, `T=sum_i n_i`, `U=N_S`, `R=sum_i binom(n_i,2)`.

For each m, call a detector cell single if it contains exactly one prime, and bad if it contains at least two. Let a be the number of single cells and b the number of bad cells. Then

`a >= T-2R`, `b<=R`.

The first inequality uses `n<=n(n-1)` for every integer n>=2. The bad cells and the U primes of S separate the single cells into at most `b+U+1` runs; empty detector cells cause no separation. Within a run, the single primes are consecutive in the full prime sequence, since the intervening strip contains no other primes.

If there is no run of r single primes, then

`a <= (r-1)(b+U+1)`.

Combining these inequalities gives

`Y:=T-(r+1)R-(r-1)U-(r-1) <= 0` on failure.

On success Y<=T. If E denotes existence of such a run, the pointwise inequality needed below is consequently `Y<=T 1_E` everywhere. We do not require every suppressed cell to be empty or every detector cell to be clean; their primes/collisions are explicitly paid for in Y.

From (1)-(4),

`liminf E_X(WY) >= H-(r+1)c k delta^2/2-(r-1)epsilon-(r-1)`

`>= 3H/4 - 1/4 -(r-1) = r/2+3/4 >1`.

All quantities subtracted have nonnegative coefficients; using their limsups is legitimate. The constant term uses `E_X W ->1`. For sufficiently large X, `E_X(WT 1_E)>=1` and

`E_X(WT^2)<=2 B_H`, where `B_H=H+cH^2`.

Cauchy-Schwarz under the nonnegative finite measure W gives

`E_X(W 1_E) >= 1/(2B_H)`.

A second application, now under ordinary averaging, gives

`|E|/X >= [E_X(W1_E)]^2/E_X W^2 >= 1/(4B_H^2 M)=:rho>0`.

This separates the detector constant, which must survive the choice of epsilon, from M, which need only be finite afterwards. It also avoids assuming that finitely many positive-probability occupancy events have positive-probability intersection.

### 2.4 Consecutiveness, bounded multiplicity and ordinary index density

Select deterministically the first run and its first r primes for each m in E. Two consecutive selected primes lie in distinct detector cells, so their distance is at least `qh+1`. It is at most T_X. Uniformly in the strip, `log p=L+O(1)`. Since `q delta>C` strictly, all selected ell gaps exceed `C log p` once X is large; they are at most `(A+1)log p`.

If p is the first selected prime, `m<p<=m+T_X`; at most T_X integers m can select this same p. Thus at least

`rho X/T_X >= (rho/A) X/log X`

distinct prime indices begin such chains. A very long external gap cannot inflate this count: the multiplicity depends only on the finite strip length.

For arbitrary large N, take `X=floor(p_N/3)`. The whole strip ends below p_N, and `X/log X~N/3` by the prime number theorem, hence `X/log X>=N/4` eventually. We obtain the statement in section 2.1 with `B=A+1` and `eta=rho/(4A)`. The choices C,r,k,delta,q,epsilon,d,f,G precede X. This completes the technical proof.

## 3. Route B: prescribed occupied windows and a joint marked lower bound

This route targets the same chain problem directly and then the genuinely stronger question of prescribed narrow gap ranges. Fix ell>=1, positive a_0,...,a_{ell-1}, and zeta>0. The proposed narrow-box target is positive ordinary lower density of indices n for which

`a_j < (p_{n+j+1}-p_{n+j})/log p_{n+j} < a_j+zeta`, all j.

Take r=ell+1 small detector windows around fixed cumulative positions, with their separations chosen strictly inside these ranges and window widths much smaller than zeta. Let S contain every other shift between the first and last window. A prime in every detector window, exactly one in each, and no prime in S would imply the target. The geometry has no difficulty; the missing lower estimate does.

Write `P_*=product_{i=1}^r N_{D_i}`, `B_*=N_S+sum_i binom(N_{D_i},2)`, and let W be a source suppression weight. A sufficient quantitative contract, for some single finite choice of W, is

(J1) `liminf E_X(W P_*)>=a>0`,

(J2) `limsup E_X(W P_* B_*)<=a/2`,

(J3) `limsup E_X(W P_*^2)<=K<infinity`, `limsup E_X W^2<=M<infinity`.

Indeed B_* is a nonnegative integer. On the bad event it is at least one, so J1-J2 leave at least a/2 weighted P_* mass on `B_*=0`. There P_*>0 means exactly one prime in every D_i. J3 and two Cauchy-Schwarz steps give positive ordinary mass, followed by the same bounded-multiplicity argument. This is a sufficient conditional reduction, not a result.

### Why the lower step is unpaid

Expanding Z^2 in J1 and fixing its divisors leaves an arithmetic progression in m weighted by

`theta(m+b_1)...theta(m+b_r)`, with distinct external b_i.

For r>=2, the marked mixed-moment proposition does not evaluate this expression. Bombieri-Vinogradov for one prime is not a distribution theorem for a prime tuple conditional on another shifted argument being prime. The deterministic deletion identity on the event that several shifts are prime does not provide a lower bound for the measure of that event.

Replacing each prime by D_G^2 goes in the wrong direction for J1. With a sufficiently small fixed support budget, the general unmarked formula can supply finite higher-moment upper bounds of the J3 type. This never supplies J1. Nor does a first-moment estimate for N_S alone give J2, because P_* can concentrate on the suppressed-prime event. Even if one controls that loss by additional upper moments and a smaller suppression tolerance, a positive joint lower mass is still required, with constants that allow the choices to close.

A direct illustration: choose 0<delta<=1/r, set W=1, let exactly one of the r windows be occupied with probability delta each, and leave all empty with the remaining probability. Then every marginal has mean delta, every within-window pair count is zero, the total second moment is r delta, the suppression count can be zero, and all moments of W are bounded. Yet `P_*=0` identically. This is a countermodel to an inference from these moment inequalities, not an asserted model for primes or a refutation of all the source's arithmetic identities.

The known exact-count theorem of Mastrostefano does not close this gap. Its Theorem 1.1 supplies a positive proportion of **one** short interval with a prescribed total prime count when its length parameter is sufficiently small depending on that count. It does not give simultaneous occupancy of prescribed separated windows under this W, or the no-prime condition in their large complement. Its section 3 uses a single-prime positive score and sieving unwanted shifts, which further confirms that importing a total-count conclusion as an independent joint law would be incorrect.

### Why Route A does not resolve the narrow target

Route A obtains some run among many windows. Its mean H=2r is made large by having many possible locations; it never forces each of r predetermined windows to be occupied. Some detector windows may be empty, so consecutive selected primes may skip many windows. The resulting B=A+1 can be large. No step makes B-C arbitrarily small, prescribes a gap vector, or yields a lower bound for J1. A pigeonhole argument selects an unspecified gap pattern, not every prescribed pattern.

## 4. Counterexample search and self-review

* A single positive-density large-gap theorem cannot be intersected with its shifts. For an explicit real-gap surrogate of mean one, set `g_{2j-1}=1/2` and `g_{2j}=(3/4)(1+v_2(j))`. The limiting frequency of `v_2(j)=t` is `2^{-t-1}`, and its mean is one (also by the elementary valuation-sum formula). Thus the mean of g is one and every fixed high threshold has positive lower frequency, while two successive g's never both exceed 1. This does not claim to construct primes. It tests and rejects the invalid density-only argument.
* Counting empty starting intervals without a bounded prime-selection multiplicity would permit a sparse set of huge gaps to dominate. The finite-strip selection in section 2.4 pays exactly this cost.
* No use is made of two actual prime marks in Route A. The pair estimate is an unmarked six-factor upper bound. The only genuine marked formulas are for the total detector count and the suppressed count.
* The finite-union extension has been written at the equality-pattern and cell-assignment level. The given equal-box singular-series lemma is sufficient; no new unequal-box or growing-dimensional theorem is silently substituted.
* Extra primes in suppressed cells are not ignored. Each is charged as a run separator. A bad detector cell is also a separator; `n<=2 binom(n,2)` pays for all its primes in the singleton count.
* Boundary primes cause no issue: cells partition the strip into consecutive integer shifts; intervals can be interpreted as half-open at integer endpoints. All chosen chains lie inside that strip and therefore are consecutive in the ambient prime sequence.
* No uniform fourth-moment constant is claimed as epsilon tends to zero. The source family is selected once, its finite M is then used, and only X tends to infinity.
* There is no growing-threshold, growing-chain, explicit-density, narrow-box, or limiting-distribution conclusion.

## 5. Contribution check and verdict

The direct source headline does not state the chain result. Against the inspected primary statements, Route A replaces an extremal chain-existence conclusion by an ordinary positive lower index proportion at each fixed logarithmic threshold. This is a real difference of counting measures. It is not evidence by itself of a new substantial contribution.

The decisive operation-level comparison is with Ford–Maynard–Tao, *Chains of large gaps between primes*, arXiv:1511.04468v1, section 3, especially page 7: they obtain many primes from a first and second moment, use pair upper bounds to exclude nearby pairs, then extract a consecutive chain. Route A uses the same type of extraction. The stronger source 026 already pays the only new analytic ingredient here: an arbitrarily suppressible complement with a family-independent detector bound. Passing from one interval to a fixed union is a finite cell expansion of its existing box lemma; no new distribution estimate or test-function construction is needed. The score Y is an elementary accounting device, not a new analytic bound.

Accordingly Route A is **TECHNICAL ONLY**, even if its exact statement has not appeared in the bounded literature search. Route B identifies a genuinely stronger joint-detection requirement but does not prove it. The literature search cannot certify worldwide novelty; it found nearby exact-count results that must not be mistaken for the missing joint theorem.

**NO VIABLE TARGET IN THIS ROUND.** There is no nomination and no increase in the finding count. Both independent acceptance gates remain with the parent. The technical chain deduction is supplied for audit/reuse; it is not an acceptance PASS. The narrow-box statement remains an attempted target with explicit sufficient estimates J1-J3, the joint positive lower bound J1 being the primary unpaid step.
