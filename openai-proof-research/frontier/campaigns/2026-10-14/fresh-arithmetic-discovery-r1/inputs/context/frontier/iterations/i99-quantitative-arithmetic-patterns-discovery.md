# I99 — Quantitative simultaneous arithmetic patterns

**Disposition: no substantial finding nominated.** C99 below remains unproved and unrefuted. This report supplies author proofs of a joint quadratic major-arc formula, a uniform minor-arc bound, a sharp conditional-mixing obstruction, a sharp Fourier-to-trilinear loss, and a coefficient-explicit counting/translation-variation bridge. These are technical partials, not an independently audited theorem or a proposed ninth finding. The strongest remaining issue is a density-preserving, two-scale construction; neither a scalar avoidance estimate nor an improved exponential sum alone supplies it.

Work is confined to the three I99-owned paths. No children, shared-index edits, staging, commits, or publication. Parent integration and separate reviews remain separate tasks. All theorems **and lower proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. No upstream-truth audit, contradiction-based synthesis, or inference from an inconsistent collection is used.

## 1. History, domain, and status of the evidence

The four ledgers were consulted and frozen before developing this direction. The accepted count is eight. The Q90/Q91 branches are closed technical; I97 and the other active scout are not read, bound, or incorporated as dependencies. Prime-predecessor parity/PD/residue/primitive-root work, joint-neighbor correlations, polynomial-twist Selmer work, and the other parked directions are excluded. A finite prime congruence calculation here is not a new prime-predecessor project.

The immutable source tree has 13,223 entries, 749 manuscript directories, and 10,373 blob positions. The search reuses the 9,340 ignored I14 originals and the I79 outside originals, through I88's augmented 10,373-row hash mapping. Of the additional 1,033 positions, 776 have PDF text representations. No whole corpus is copied or downloaded. `search-domain.json` records each original path, local original, Git blob identity, original SHA-256, text representation, and text SHA-256. `lexical-search.json` retains every occurrence, exact regular expression, match, line text, character offset, and multiplicity. Its six searches have respectively 85, 139, 168, 1,159, 224, and 127 occurrences. This is **full-domain lexical search**, not full semantic reading.

`passages.json` identifies the actual source sections read, with exact ranges and hashes; `source-contracts.json` records the contract comparisons. All pinned links use the immutable commit. Literature retrievals retain raw responses, versions, URLs, status codes, hashes, and failed attempts. The nonexistent Altman–Sawhney v2 HTML request and the SIAM direct-fetch 403 are retained as failures, not described as successful full-paper reads. The available Altman–Sawhney version is v1. The initial optional BeautifulSoup extraction failed because the module was absent; the successful text conversion uses Python's standard HTML parser, preserving math `alttext`.

Source `.tex` passage locators use **LF-delimited lines** (`text.split('\n')`, a terminal empty element omitted). The lexical search uses Python **`splitlines()`**, which also splits form feeds; these conventions differ for PDF extractions and are not silently interchanged. Primary-paper citations below use theorem/section names. Only three relevant pinned PDFs are selectively re-extracted for provenance comparison, plus the downloaded Peluse–Prendiville PDF; this is not universal PDF re-extraction or proof verification.

## 2. Exact source contracts and early screening

**AP** = [Quasipolynomial Bounds for Arithmetic Progressions, September 23](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026). `ap:main` bounds the largest subset of `[N]` avoiding a nonconstant **linear** k-term AP by `C_k N exp(-c_k(log N)^{epsilon_k})`, for each fixed k. `ap:increment` and `ap:absolute` require progression-free support. Their polynomial cells allow unrestricted coefficients, but that freedom describes cells, not arbitrary forbidden polynomial configurations. The complete proof of `ap:absolute` was read, including its dependency on the positive **linear progression** counting rule. The weighted consequences already include stronger weighted reciprocal criteria.

**IP** = [Intersective polynomial differences, October 5](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-saving-for-intersective-polynomial-differences-with-an-exponent-depending-only-on-the-degree-October-5-2026). `thm:main`: for every k>=2, a c_k>0 works for every fixed intersective h of degree k and positive leading coefficient, with C_h and N_h depending on all coefficients. It concerns one difference h(n), n positive integer, with zero values exempted. `tuple:laws`, `tuple:conditional-mixing`, `tuple:covariance`, and `kernel:estimate` were read through their full proofs and endings. The cycle can have many slots, but each edge is constrained separately to the polynomial value set. This does not synchronize its argument with the argument on another edge. The kernel realizes one edge marginal and invokes a bilinear Plancherel identity.

**PP** = [Polynomial differences at prime arguments, October 5](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Power-Saving-for-Polynomial-Differences-at-Prime-Arguments-October-5-2026). `thm:main` requires a unit root modulo every modulus, degree >=2, and positive leading coefficient. It gives C_h N^(1-c_h), with **both** constants polynomial-dependent. Its complete kernel construction, major/minor comparison, unit means, and ordered-pair cancellation proof were read. It uses the stronger September 30 7/8 zero-free companion, not merely exclusion of exceptional real zeros. No new prime-distribution claim is derived here. Replacing integers by primes in C99 is outside the target.

**SF** = [Squarefree quartics and power-free values, September 24](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026). The main theorem has fixed irreducible degree d in [4,8], power k=d-2, and exact admissible Euler-product density, with no height-uniform error. More decisively, `cor:separable-products` **already states simultaneous values** for any fixed finite family of separable polynomials whose irreducible factors have degree <=k+2. Shared factors are allowed. The joint excluded residue set is the union of the individual sets modulo p^k. The full sieve-transfer and simultaneous-product proof were read through the ending: finitely many contents, discriminants and resultants are isolated, large-prime tails are union-bounded, then the two limits are taken in their prescribed order. This is an exact duplicate for the fixed-family proposal.

**OI** = [Additive indecomposability of the primes, September 24](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/the-additive-indecomposability-of-the-primes-September-24-2026). `cor:ostmann` and `thm:main` concern eventual equality, simultaneously retaining coverage of every sufficiently large prime and exclusion of composite sums. The fixed-shift sieve/finite-summand proof and complete final symmetrization were inspected. Its final lower bound inherits exact coverage and fixed data of a hypothetical decomposition. It is not an approximate-prime-coverage or arbitrary-pattern counting theorem. No robust inverse-Goldbach theorem is nominated by deleting that hypothesis.

The complete-tree title search and full-domain expressions include the earlier square-difference paper and the van der Waerden companion. Their roles are scalar power-saving and coloring estimates, respectively. The October 5 IP and PP contracts, including IP's lower tuple construction, are the strongest relevant pinned difference inputs located. No inference of semantic completeness is made from the search.

Four exact initial targets were screened:

1. **Fixed simultaneous squarefreeness.** For fixed r and separable F_i with factor degrees <=4 and joint p^2 admissibility, prove a positive density of n with all F_i(n) squarefree. Rejected as **explicit SF corollary**, including shared factors and joint local factors. Growing r or growing coefficient height is a different theorem; the source's fixed finite bad-prime set and constants do not provide that uniformity.
2. **Uniform single-polynomial prime avoidance.** Seek c_k,C_k,N_k depending only on degree, with the PP bound valid for every height and N>=N_k. **Falsified as stated:** h_H(t)=H(t-1)^k is prime-intersective and every nonzero h_H(p)>=H. For N<H, A=[N] avoids them. Choosing H after N contradicts a height-free power bound. The meaningful variant permitting C_h,N_h but requesting c_k is not falsified; a normalization/prime-progression adaptation would need accounting, and no substantiality claim is made for such an extraction.
3. **Square-step APs.** For fixed k>=3, seek `r_{k,square}(N)<=C_k N exp(-c_k(log N)^epsilon_k)` for x,x+t^2,...,x+(k-1)t^2, t>=1. Not established by AP or IP. It is not rejected as false or as an established duplicate. The strongest inspected external reduction, Altman–Sawhney v1, keeps a homogeneous model when the lowest degree is >1 and has its own quantitative transfer loss. This remains a possible target, but no new mechanism was found here; it is not selected for the detailed routes.
4. **Uniform nonlinear Roth family C99**, stated next. Selected because the different degrees require common-parameter information genuinely absent from all five stated contracts, and both candidate proof mechanisms can be tested precisely.

Local obstructions are not omitted. Each of t^2 and (t-1)^2 is intersective, but they are not jointly intersective modulo 2; the even integers avoid x,x+t^2,x+(t-1)^2. Separately squarefree-admissible F_0(t)=t^4+4 and F_1(t)=(t-1)^4+4 have no joint squarefree input: one value is divisible by 4 at every t. They are separable (the derivative and polynomial have no common zero), and no odd fixed prime square divides either, as evaluation at 0 or 1 gives 4. Thus the joint SF condition is essential. These are actual polynomial counterexamples to the proposed shortcuts, not abstract marginal models.

## 3. The selected target and literature comparison

**C99 (unproved target).** There exist absolute C>=2 and B>=2 such that for every positive integer q, every 0<delta<=1, every integer N>=2 with

    log N >= C (log(2q)+log(2/delta))^B,

and every A subset [N] with |A|>=delta N, there are integers x and t>=2 with

    x, x+t, x+q t^2 in A.

There are exactly two polynomials, with one **common integer parameter** t and one **common base** x. Their degrees are 1 and 2, their leading coefficients are 1 and q, their constant terms vanish, and their coefficient height is max(1,q). Both vanish at t=0 modulo every modulus, so simultaneous intersectivity holds. The threshold handles the archimedean obstruction when q is large. At fixed q it asks for a stretched-exponential density saving in log N. No prime parameter, arbitrary family, growing number of polynomials, or coefficient-independent all-N power saving is asserted. Requiring t>=2 makes all three entries distinct and removes at most |A| terms from the usual t>=1 count.

This is a quantitative strengthening of the **nonlinear Roth / polynomial Szemerédi problem**, not a claim to solve the unrestricted polynomial Szemerédi problem. The inspected primary literature supplies observed significance without a ranking: Peluse–Prendiville, [arXiv:2003.04122v2](https://arxiv.org/abs/2003.04122v2), Theorem 1.1, improves the nonlinear Roth density bound to a power of log N. Their §§2–6 describe the local inverse, regularity, density-increment, and major-arc mechanisms; these relevant proofs were read through their endings. The arXiv version page still identifies v2 (14 September 2021) as current, and records the 2022 IMRN publication.

Shao–Wang, [arXiv:2505.16822v2](https://arxiv.org/abs/2505.16822v2), Theorems 1.1–1.3 and 2.4, treats general distinct degrees, with polynomial-dependent logarithmic exponents, and gives a popular-difference statement. The complete §4 proof was read, including regularity, density increment and terminal iteration. Its `P_1=t,P_2=q t^2` family fits the `(1,q)` coefficient convention. This is an important stronger companion to the older discussion of an unresolved longer-pattern inverse theorem. It does not state C99's logarithmic-height/quasipolynomial threshold.

Altman–Sawhney, [arXiv:2506.13010v1](https://arxiv.org/abs/2506.13010v1), Theorem 1.1 and Lemma 2.11, supplies integer transfer for common polynomial differences. The complete final transfer deduction (§2.4) was read. Its comparison error is `exp(-(log log N)^{Omega(1)})`; the model for lowest degree >1 is still homogeneous. Updating only a linear-AP input therefore does not, within that displayed proof, remove both limitations. Its more general transferable-pattern theorem is over prime cyclic groups; that category is not silently substituted for integer intervals of parameter length sqrt(N/q).

A targeted MathDB search did not locate a verified specific page for C99. No page ID or priority assertion is invented. A 2026 Peluse ICM article was located, but direct archival retrieval returned 403; it is not relied on for a new proof operation. The above primary papers suffice to identify the named problem and quantitative baseline. “No duplicate found in these sources” does not certify worldwide novelty.

## 4. Route A: construct the joint quadratic kernel

Write e(u)=exp(2 pi i u). For integers M,q>=1 and a periodic complex weight w of period D, define

    S_w(alpha,beta) = M^(-1) sum_{1<=t<=M} w(t)e(alpha t+beta q t^2).

This is the actual joint multiplier, not a product of the multipliers of t and qt^2. Dropping t=1 changes it by at most ||w||_infty/M. In this section q is explicit and may vary.

### A1. Paid joint major-arc estimate

Let r>=1 and a,b be integers, alpha=a/r+sigma, beta=b/r+tau, and L=lcm(D,r). Put

    G_w(a,b;r)=L^(-1) sum_{t mod L} w(t)e((a t+bq t^2)/r),
    I_M(sigma,tau)=M^(-1) integral_0^M e(sigma u+tau q u^2) du.

Then, for every choice of these data,

    |S_w-G_w I_M|
    <= (2L||w||_infty/M)
       (1+2 pi |sigma|M+2 pi |tau|qM^2).                 (A1)

In particular the error is O(L||w||_infty/M) on the anisotropic box
`|sigma|<=1/M`, `|tau|<=1/(qM^2)`, with an absolute constant.

**Proof.** The sequence c(t)=w(t)e((a t+bq t^2)/r) has period L and mean G_w. For real v>=0, its partial sum minus G_w v has modulus <=2L||w||_infty, by splitting into complete periods and the last incomplete period; the fractional last interval is included in this bound. Stieltjes partial summation against F(u)=e(sigma u+tau q u^2), starting at 0, bounds the discrepancy by this supremum times `1+integral_0^M |F'|`. The latter integral is at most `2 pi(|sigma|M+|tau|qM^2)`. Divide by M. This proves every claimed constant and needs neither positivity nor a fixed-height hypothesis. ∎

The local factor must remain joint. For odd r and w=1 set g=gcd(bq,r). Then

    |G_1(a,b;r)| = 0                 if g does not divide a,
                    sqrt(g/r)       if g divides a.     (A2)

This includes g=r, when the value is 1 or 0. For even moduli A1 remains valid but A2 is not asserted; their local factor is retained exactly.

**Proof.** Translation t -> t+r/g leaves the quadratic phase invariant and multiplies the linear phase by e(a/g), proving the zero case. If g|a, divide the phase and modulus by g; the sum reduces to modulus r'=r/g with gcd(bq/g,r')=1. If r'=1 it equals 1. Otherwise square its absolute value, put h=t-s, and average first in s. Since r' is odd, the linear coefficient `2(bq/g)h` is a unit times h, so only h=0 survives. Its squared normalized magnitude is 1/r'. ∎

### A2. Paid weighted minor-arc estimate

Use normalized Fourier coefficients of w modulo D and write
`A_w=sum_{j mod D}|w_hat(j)|`. Suppose `theta=2q beta` has a reduced rational approximant c/r with

    1<=r<=M^2,   |theta-c/r|<=r^(-2).

Then, uniformly in alpha and all the other data,

    |S_w(alpha,beta)|
    <= C A_w [log(2M)(r^(-1)+M^(-1)+r/M^2)]^(1/2),     (A3)

for an absolute constant C. Consequently, if 0<eta<=1 and
`M^eta<=r<=M^(2-eta)`, the bound is
`C A_w sqrt(log(2M)) M^(-eta/2)`.

**Proof.** For an unweighted sum T, squaring and grouping pairs by h gives

    |T|^2 <= M+2 sum_{1<=h<M} min(M,1/(2||theta h||)).

The convention at zero is M. For r>=2 split the h indices into blocks of length max(1,floor(r/2)). Within a block, distinct residues have circle separation at least 1/(2r): for 0<d<r/2 the approximation error is <=d/r^2, while ||cd/r||>=1/r. Each block therefore contributes O(M+r log(2r)), by ordering distances to zero. There are O(M/r+1) blocks. Dividing by M^2, expanding the product, and using r<=M^2 gives the square of (A3) with A_w=1. For r=1 the asserted estimate follows from |T|<=M. Finally expand w into its D Fourier modes. Each changes only alpha, so triangle inequality gives A_w times the same bound. ∎

These are complete estimates in their stated ranges. They are **not** a globally assembled two-variable model with a small trilinear comparison norm. In particular, A3 handles a specified quadratic minor-arc range, not every frequency outside a joint rectangular major-arc set. Claiming more would discard the linear-frequency and transition regimes.

### A3. Why the source's higher-lift cancellation cannot just be copied

Fix an odd prime p, q with p not dividing q, and r mod p. Put t=r+ps modulo p^2. The joint values `(t,qt^2)` have exactly p lifts of `(r,qr^2)`; the full two-coordinate residue coset has p^2 elements. More decisively, the **primitive** character of denominator p^2 with coefficients `(-2qr,1)` is constant on these lifts:

    -2qr(r+ps)+q(r+ps)^2 = -qr^2+qp^2s^2.

Its mean has modulus one. This proves an actual local obstruction to a vector version of IP `kernel:coefficients` that annihilates every primitive higher-conductor character. It does not contradict the scalar lemma: a one-dimensional curve cannot be uniform among all two-dimensional lifts. Retaining tangent/normal characters, instead of discarding every higher conductor, is a necessary change for this attempted route.

### A4. Sharp limit on tuple conditional mixing

**Proposition A4.** Let Z be F_p-valued and let Y contain all the other tuple coordinates. Suppose for every nonzero s mod p,

    || E(e_p(sZ) | Y) ||_2 <= rho,    0<=rho<=1.

For every F_p-valued function F(Y),

    Pr[Z=F(Y)] <= 1/p+(1-1/p)rho.                       (A4)

This is sharp, even with uniform individual marginals for a parabolic triple.

**Proof.** Character orthogonality expresses the probability as `p^(-1) sum_s E[e_p(sZ-sF(Y))]`. The zero character gives 1/p. For each other character, condition on Y and apply Cauchy–Schwarz against the unit-modulus function e_p(-sF(Y)). Its absolute contribution is <=rho/p. Sum. For sharpness take independent uniform X,T, put Y=(X,X+T), and with probability rho set Z=X+qT^2; otherwise choose Z independently uniform. Each coordinate is uniform, each nonzero conditional character equals rho e_p(s(X+qT^2)), and equality holds in (A4). ∎

IP's mixing property `eq:8` has rho=p^(-gamma) for every individual coordinate against all the remaining labels. If three designated slots must satisfy `z_2-z_0=q(z_1-z_0)^2` outside exceptional mass epsilon, then

    epsilon >= 1-1/p-(1-1/p)p^(-gamma).

Thus an exceptional mass p^(-4), or any epsilon tending to zero, is incompatible with the **unchanged** source mixing property for that designated triple. Adding more slots does not help: Y still contains the two determining coordinates. The sharpness example concerns the specified output coordinate, not an assertion that every coordinate of that example satisfies the same bound. A block-level or differently conditioned construction might evade this obstruction; it has not been built here.

### A5. The precise analytic norm loss

On G=Z/pZ use normalized averages, normalized Fourier coefficients, and

    T_K(f_0,f_1,f_2)=E_{x,u,v} K(u,v)f_0(x)f_1(x+u)f_2(x+v).

For arbitrary complex K and 1-bounded f_i,

    |T_K| <= sqrt(p) ||K_hat||_infty product_i ||f_i||_2. (A5)

**Proof.** Fourier expansion gives a sum over a,b of
`f0_hat(-a-b)f1_hat(a)f2_hat(b) K_hat(-a,-b)`.
For each b, Cauchy–Schwarz bounds the sum over a of the first two absolute factors by `||f0||_2||f1||_2`. Sum |f2_hat(b)| and apply Cauchy–Schwarz on p frequencies. Parseval gives (A5). ∎

The factor sqrt(p) is sharp. For c nonzero modulo odd p, set

    K(u,v)=p 1_{v=-u} e_p(2cu^2),
    f_0(x)=e_p(2cx^2),   f_1(x)=f_2(x)=e_p(-cx^2).

Here E|K|=1, all ||f_i||_2=1, every Fourier coefficient of K has modulus p^(-1/2) by A2, and direct substitution gives T_K=1. This is not merely a count of frequencies. For a real signed kernel take Re K: its Fourier supremum is <=p^(-1/2) and the same test has value `(1+E_u e_p(-4cu^2))/2`, of modulus at least `(1-p^(-1/2))/2`. Thus even real signed kernels of bounded total variation have this obstruction in order of magnitude.

This does not show that the **actual parabolic kernel** has a large comparison error. It disproves an unqualified, dimension-free trilinear analogue of the scalar sup-Fourier/Plancherel step. A new estimate must exploit the actual curve and its input functions, or use a stronger norm. Together A3–A5 explain why paying Weyl errors alone does not finish C99.

## 5. Route B: density increments and a paid translation bridge

A second route uses the two physical scales instead of trying to extend the source's tuple law. There is an exact progression covariance:

    a+d(x,x+t,x+(qd)t^2)
      = (a+dx, a+dx+dt, a+dx+q(dt)^2).                 (B1)

Thus restriction to a progression of stride d changes q to qd. This is not the single-polynomial auxiliary family with a freely chosen separate argument on each edge.

### B2. Coefficient-explicit counting from translation stability

Here is a positive bridge, with all constants and dependencies visible. Fix once and for all constants C>=1 and 0<c<1 from the stipulated square-difference theorem, enlarged to ensure `alpha_square(L)<=C L^(1-c)` for every integer L>=1. This follows from IP `thm:main` at h(t)=t^2 by incorporating its finite threshold in C.

Let N,q,D be positive integers, A subset [N], a=|A|, Q=qD^2, and

    M=floor(sqrt((N-1)/Q)) >=1,
    L=ceil(N/Q),   B=min(N, Q C L^(1-c)),
    V_D(A)=|{x in A : x-D not in A}|.

Extend 1_A by zero outside [N]. Let T count pairs (x,t) with t in `{2,...,M}` and

    x, x+Dt, x+qD^2t^2 in A.

Then

    2T >= a^2/B - 3a - V_D(A) M(M+1).                 (B2)

This holds for all q,D in the indicated range; **C and c do not depend on q or D**. A negative right side is simply uninformative. In particular, a C99-avoiding set satisfies the necessary bound

    V_D(A) >= max(0, (a^2/B-3a)/(M(M+1)))              (B3)

for every such D. This is an author-level technical consequence of the scalar input plus a new explicit error accounting, not a density theorem for arbitrary A.

**Proof.** Construct the simple graph on [N] with an edge between x and x+Qt^2 whenever 1<=t<=M and the endpoints lie in [N]. Each pair determines at most one positive t. In each residue class modulo Q, an independent set becomes a square-difference-free subset of an interval of length at most L. There are at most Q classes, so the graph independence number is <=Q C L^(1-c), and also <=N. It is therefore <=B.

Let E be the number of edges induced by A. A random ordering of A supplies an independent set consisting of vertices preceding all their neighbors, with expected size `sum_{v in A} 1/(deg_A(v)+1)`. Cauchy–Schwarz bounds this below by `a^2/(2E+a)`. Hence `2E>=a^2/B-a` (also true when a=0).

For any positive s, let `D_A(s)=sum_x 1_A(x)(1-1_A(x+s))`. Finiteness gives `D_A(s)=||1_A(.+s)-1_A||_1/2`. Telescoping translations therefore gives `D_A(Dt)<=t V_D(A)`; `D_A(D)=V_D(A)` because beginnings and ends of the finite D-chains have the same number. Every square edge not counted as a triple has its middle point x+Dt missing. Its number for this t is <=D_A(Dt). Consequently the triple count with t>=1 is >=`E-V_D(A)M(M+1)/2`. Removing t=1 loses at most a. Combine with the lower bound on E to prove (B2). If A has no C99 triple, then no positive restricted t>=2 contributes, proving (B3). ∎

Unlike substituting qt^2 into IP, this estimate keeps the **same t** in both shifts and pays every missing-middle-point error. It gives an actual counting result when the right side is positive. It does not assume the shifted memberships are independent. It also shows exactly why a scalar bound alone is too weak: for an arbitrary A, V_D may be as large as a, while B2 would need roughly `V_D << a^2/(B M^2)`. No bound of that strength for a dense subcell has been obtained. A set which is a union of a few ordinary intervals is not a promising substantial subclass: avoiding t=2 already bounds the length of each ordinary interval. No such easy subclass is nominated.

### B4. Iteration cost and the attempted AP-cell shortcut

Peluse–Prendiville's Lemma 2.1 and its complete proof give a fixed proportional density increase on a progression, but retain a square-root length scale and coefficient growth. In their normalization the new stride is q b, so the new coefficient is q^2 b. Shao–Wang's current Lemma 4.2 and subsequent proof retain the ratio `deg P_1/deg P_2=1/2`, with an explicit growing auxiliary coefficient. These are available methods, not missing lemmas being relabeled as discoveries.

The cost is already visible in the following exact scalar calculation. Put r_j=log q_j, ell_j=log N_j. Suppose the supplied bounds at a sequence of increments have the form

    r_{j+1} <= 2r_j+E,
    ell_{j+1} >= ell_j/2 - K r_j-E,

where K>=0 and E>=0 are fixed upper budgets for the run. Then

    r_j <= 2^j r_0+(2^j-1)E,
    ell_j >= 2^(-j)ell_0
      -K(r_0+E)(2^(j+1)-2^(1-j))/3 -2E.              (B4)

**Proof.** Induct on the first recurrence. Substitute its upper bound, weakened to `2^j(r_0+E)`, in the second, then iterate the affine inequality. The exact convolution is
`sum_{i=0}^{j-1} 2^{-(j-1-i)}2^i=(2^{j+1}-2^{1-j})/3`;
the sum of the constant error weights is <2. This proves (B4). ∎

With j of order log(1/delta), merely improving E to a polynomial in log(1/delta) leaves powers of 1/delta through the factors 2^j and 4^j. This statement is about the **guarantee of this recurrence**, not an impossibility theorem for all density increments: an actual increment might be much larger than its lower bound. The computation explains why the source AP theorem's favorable precision recurrence cannot just be appended at the end.

There is also a concrete support problem with applying AP `ap:absolute` directly. Let H>=3 and d>H, and take A=d[H] inside [dH]. It contains an H-term linear AP. But if x,x+t,x+t^2 all lie in A, then d|t and `t^2<=d(H-1)<d^2`, impossible for positive t divisible by d. Thus nonlinear-Roth-free support need not satisfy the source's linear progression-free hypothesis even on arbitrarily long finite APs. This does not conflict with C99: its example has density 1/d, outside the proposed quasipolynomial threshold at these scales.

The attempted repair is to carry a short-scale translation statistic (such as V_D or an appropriate averaged replacement) alongside the old polynomial-cell equations, use B2 to force a count on a stable cell, and otherwise increase density using the detected translation instability. B2 pays the count in the stable case. The unstable-case selection, with only polynomial logarithmic cumulative losses and with q tracked under (B1), is **unpaid**. No such two-scale dichotomy is asserted. Neither AP's linear counting input nor SF/OI supplies it.

## 6. What is proved, what remains, and contribution limits

- **Stipulated source results:** AP/IP/PP/SF/OI and all their lower operations. Their truth is assumed as requested; this report is not an independent audit of them.
- **Author proofs, technical:** A1–A2 (joint local approximation and exact odd-modulus factors), A3's weighted Weyl estimate, the p^2 normal-character obstruction, A4 (sharp deterministic prediction bound), A5 (sharp trilinear multiplier loss), B1–B4, and the explicit polynomial/local/support counterexamples.
- **Falsified proposals:** height-free all-polynomial single-pattern power bounds; replacing joint local admissibility by individual admissibility; unchanged all-coordinate source mixing with an almost-sure designated parabolic triple; lossless general trilinear transfer from scalar Fourier supremum; direct identification of nonlinear-free with AP-free support.
- **Unresolved:** C99; the alternative square-step AP target; a suitable structured trilinear comparison or two-scale density increment. A1/A3 do not constitute a full major/minor-arc assembly, and B2 does not control V_D for arbitrary dense sets.
- **Contribution:** no positive substantial candidate for parent review. The paid estimates use elementary harmonic, graph, and translation operations with the stipulated scalar theorem. They are retained as precise technical bridges and method obstructions, not split into findings or advertised as literature-first results.

For the parent, the actionable next prerequisite is specific: either construct a block-conditioned tuple/cut-norm estimate compatible with the parabolic relation and its higher-conductor normal characters, or prove a density/stability alternative that makes the right side of B2 positive after only polynomial logarithmic losses. A claim that the new theorem follows merely by running the scalar kernel twice fails to address both A4 and the shared middle-point error in B2.

## 7. Replay contract

Run from the project root:

    python -B frontier/experiments/i99_quantitative_arithmetic_patterns_discovery/verify.py

The final verifier is offline and read-only: no downloads, writes, bytecode, repairs, or resealing. It checks the exact owned inventory, every immutable reference and original blob identity in the domain, the lexical occurrence multisets, precise passage hashes, selective PDF extraction bytes, and exact finite diagnostics. The only permitted external reference drift is the four named live ledgers; their frozen snapshots remain immutable. No active I97 or other-scout artifact is a dependency. The seal is made once after prevalidation; its own bytes are identified by the final handoff hash, rather than a circular self-hash. Earlier retrieval/extraction failures remain recorded.

The finite diagnostics check 20,825 odd-modulus Gauss cases, 606 primitive normal-character cases, 3,650 chirp identities, 10,688 counting/variation cases with exactly computed finite independence numbers, 1,568 covariance identities, thirteen resource convolutions, twelve sharp mixing examples, and two local-obstruction examples. These are exact arithmetic diagnostics. Neither they nor source hash replay constitute a universal analytic proof, contribution decision, human review, or formal certification.
