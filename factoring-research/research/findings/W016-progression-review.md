# W016 independent review: sparse progression transfer and its comparator

2026-10-08. **Accept the transfer and nonzero recovery with the contract below; repair the comparison by batching the supplied progressions themselves. Verified new complete factoring improvement: NONE.** Parent remains principal researcher. This review is symbolic: no factoring experiment, numerical certificate, parameter search, install, delegation, commit, shared-code edit, or Lean claim.

The useful additional result is an explicit evaluator for varying-modulus progression products in `O~(J+sqrt(V))`, where `J` is the number of supplied interval records and `V` their total candidate length, counted with multiplicity. Consequently beating `sum sqrt(L_j)` by sharing certificates is not enough. A separate, constructive linear-certificate calculation gives conditional search cost `O~(N^(1/5)/m^(1/5))` on a balanced supplied progression for `m<=N^(1/6)`. An elementary random-order argument below also pays for base acquisition in that regime, giving an expected bound **on the supplied promise**. Deterministic acquisition and N-only coverage remain separate. Neither construction supplies an improved N-only splitter.

**Frozen scope.** The [original brief](W016-progression-review-evidence/original-brief.txt) and [input manifest](W016-progression-review-evidence/input-manifest.json) retain the instructions, all of W016, and the relevant accepted dispositions. W014's dense-grid and full-image results keep their original scopes. W013's accepted extraction contract is reused, not re-audited in full. W015's monic evaluation/recovery argument is used; its separate valuation-compression lemma is not audited. Source snapshots, failed retrieval, and inspection scope are retained in the evidence directory. No novelty claim follows from this narrow review.

**Transfer, domain, and recovery.** Let `N>1` be composite, `p|N` prime, `Q=N/p`, `m,q>=1` integers, and `p=1+mt` with positive integer `t`. Require `A in Z[T]` and `alpha in (Z/NZ)^*`. Put

```
beta = alpha^m mod N,
D = A(0)-qN,             e = A(t)-qQ.
```

There is an integer `C(t)` with `A(t)-A(0)=t C(t)`. Thus

```
D-e = -t C(t)-q(N-Q) = -t(C(t)+qmQ),
beta^t = alpha^(p-1) = 1 mod p,
beta^D = beta^e mod p.                                      (1)
```

Negative exponents use a checked inverse modulo N. The argument needs neither a prime cofactor nor squarefreeness. It establishes a congruence modulo p, not automatically modulo p's full power in N.

For every candidate integer error `e'`, recover integer roots in the recorded interval of

```
F_i,e'(T) = (1+m_i T)(A_i(T)-e')-q_i N.                     (2)
```

This polynomial is nonzero: its value at the rational point `-1/m_i` is `-q_i N`. Its degree is at most `deg(A_i)+1`. For a recovered integer T, accept only `d=1+m_i T` satisfying `1<d<N` and `d|N`. At the true error, t is a root. Other global exponent matches do not prove an integer equality and must undergo this recovery. Constant A, negative errors, repeated roots, and prime powers cause no exception to this argument.

“Integer polynomial” must mean integer **coefficients** here. Integer-valued rational polynomials do not generally satisfy `t | A(t)-A(0)`; for example `A(T)=T(T-1)/2` has `A(2)-A(0)=1`. Their earlier denominator-clearing contract cannot be omitted. If coefficients are supplied in local coordinates `u=T-a`, the public exponent is `A_local(-a)-qN`, not `A_local(0)-qN`.

The degree-independent exponent m is valid for this residue-1 construction. It avoids the indicated degree-dependent clearing in that particular representation. It is not a lower bound on other representations of general residue classes. Exact dense-polynomial integer-root isolation has polynomial bit cost in degree, coefficient height, and endpoint bit lengths, as accepted in W014. Growing degree is therefore allowed, but its input size and every recovery invocation remain charged. A small circuit describing exponential degree does not supply a cheap dense expansion or root routine.

For `f(T)=qN/(1+mT)`,

```
f''(T) = 2qNm^2/(1+mT)^3.
```

Thus the t-grid is consecutive in its own coordinate, with curvature scale `qNm^2/X^3` near `p~X`. W014 cannot be applied using the old curvature or the old number of consecutive p-values. Conversely, changing coordinates does not nullify its rescaled hypotheses. A physical width `mH` has the same Taylor curvature contribution `qN(mH)^2/X^3`. Sparse-grid syntax by itself produces neither coefficients nor coverage.

**Corrected conditional consumer.** Distinguish `J` supplied progression intervals from `K` certificate records; many certificates may subdivide a single progression. Empty intervals are discarded, and candidate values are clipped to `(1,N)`. For certificate i supply `m_i`, an integer t-interval, `A_i in Z[T]`, integers `q_i>=1,E_i>=0`, and a valid bound

```
|A_i(T)-q_i N/(1+m_i T)| <= E_i
```

throughout its claimed domain. It suffices that at least one prime factor belongs to a certified domain. Supplying or proving that coverage is a separate premise.

Supply a **common** unit beta for which (1) holds for each certificate's possible covered prime. Let `B>=1` be an integer and assume `ord_N(beta)>=B`, obtained at a charged cost. Generate babies `beta^j`, `0<=j<B`, and check `gcd(beta^j-1,N)` for `1<=j<B`. A nonunit gcd is proper under this order assumption and finishes. Otherwise `ord_r(beta)>=B` for every prime `r|N`, including prime-power components. Merely having distinct babies modulo N would not establish this fact.

Put

```
w_i = 2E_i+1,        S = sum_i w_i,
G(B) = sum_i ceil(w_i/B),
gamma_i,k = beta^(D_i+E_i-kB),   0<=k<ceil(w_i/B).           (3)
```

Use the accepted W013 tagged global-match procedure with recovery (2). In particular, check every tag before removing a globally matching giant; a final partial block may be searched with its harmless extra errors, or invalid errors may be filtered. Componentwise uniqueness ensures a true collision cannot be removed unsuccessfully. After removal, evaluate the monic product of remaining giant differences at all babies. A nonunit value either splits N or, for a full product gcd, yields a proper factor after **one** scan/descent to a nonunit leaf: every retained leaf difference is nonzero modulo N. This works for arbitrary prime powers. It does not require factoring polynomials over an unknown finite field.

For fixed degree and polynomial-logarithmic parameter/coefficient widths the full conditional bound is

```
C_prog,bit + C_cert,bit + C_base,bit
       + (K+B+G(B)) poly(log N).                            (4)
```

Here `C_prog` includes obtaining/validating coverage and all progression records; `C_cert` includes generating/certifying A,q,E; `C_base` includes common-base construction, failed attempts, and order acquisition. The list term includes gcds, sorting, all tags, arithmetic, storage traffic, all global-match root checks, and recovery. For growing degree/height, retain their actual read/expansion costs and the sum of root costs over the at most G global tags; do not hide them in a factor depending only on log N. Likewise giant initialization pays the bit length of `D_i+E_i`, not its value as a unit-cost integer. List-index logarithms must also be charged if counts exceed `N^O(1)`.

An operational version may instead build/check the B babies without a supplied global-order certificate. It returns a proper factor on a proper gcd, continues only if all checks are units, and returns **ORDER-FAIL** if some checked power equals 1 modulo N. That last branch is not a factoring success or a free restart. With `B=1` it always has a valid table but generally pays the whole error list. The guarantee in (4) is conditional on a usable base or a proved, paid factor-or-base acquisition algorithm.

**Varying m and common powers.** For one m, use `beta=alpha^m`. For varying moduli, a sufficient explicit construction is

```
M = lcm(m_1,...,m_K),      beta = alpha^M mod N.
```

Equivalently `alpha_i=alpha^(M/m_i)` gives `alpha_i^m_i=beta`. These auxiliary alpha_i need not be computed: just compute M and the one common beta. Because `m_i|M`, `beta^t=alpha^((M/m_i)(p-1))=1` on certificate i's promised factors, so the **unscaled** D_i and errors still work.

The exact order losses, for `r=ord_p(alpha)` and `r_i=ord_p(alpha^m_i)`, are

```
ord_p(beta) = r/gcd(r,M)
            = r_i/gcd(r_i,M/m_i)
           <= (p-1)/gcd(p-1,M) <= (p-1)/m_i = t.            (5)
```

The last inequality is at a factor promised by i. The analogous identity holds for ord_N. Large order of alpha alone is insufficient. A sufficient global-order input is `ord_N(alpha)>=MB`, but this can be wasteful or impossible; the exact gcd formula is sharper. If `p-1|M`, beta is 1 modulo p. This can reveal a proper gcd immediately, or can cause global order failure; it must not be described as always helping or always defeating factoring.

Extra order loss is not inevitable: if `gcd(r_i,M/m_i)=1`, there is none beyond the original power m_i. For example, with power-of-two moduli and odd residual order r_i this holds. It is an additional condition, not a coverage/order theorem for N alone. The lcm construction is sufficient, not a claim that every possible common base must arise this way.

Charge M's construction and binary size; `log M<=sum log m_i` may be much larger than log N. Modular powering costs that many exponent bits. No unknown group order is available to reduce M for free. Alternatively group certificates by their actual common base and pay

```
K + sum_g (B_g + sum_(i in g) ceil(w_i/B_g))
```

plus acquisition. Cross-matching unrelated bases does not silently supply the per-base giant grids or justify global-match removal. No varying-m certificate family in W016 is supplied with a proof that lcm powering preserves the needed order at the proposed cost.

**The matched product comparator, including a stronger family algorithm.** One interval has candidates `1+mT` for `a<=T<a+L`; require these ordinary integers to lie in `(1,N)`. For nonempty intervals with positive T, `m<N`. Compute `gcd(m,N)`: a nonunit gcd is already a proper factor. Otherwise form `c=m^(-1) mod N`. Then

```
product_(T=a)^(a+L-1) (1+mT)
       = m^L product_(u=0)^(L-1) (a+c+u) mod N.            (6)
```

The scalar is a unit. Build the monic polynomial `F_b(Z)=product_(u=0)^(b-1)(Z+u)`, evaluate at complete b-block starts `a+c+kb`, and handle a tail of fewer than b factors. With `b=ceil(sqrt L)`, cost is `O~(1+sqrt L)` including construction. This proves W016's elementary comparator with the required slope-unit branch. For a range through `O(sqrt N)`, `L=O(1+sqrt N/m)` and the bound is `O~(1+N^(1/4)/sqrt m)`; the additive one matters when the grid is short.

Equation (6) does more: the **same F_b** serves different m, because only the evaluation shift `a+m^(-1)` changes. Here is the full unequal-length construction for J records, `V=sum_j L_j`.

1. Split each length into consecutive power-of-two pieces. There are at most `1+floor(log2 L_j)` pieces for record j. Group pieces by length `ell=2^h`; retain their parent records and shifts. Occurrence length is still V.
2. For a group with v pieces, choose w to be the largest power of two at most `min(ell,sqrt(v ell))`. Since `w|ell`, there are exactly `Q=v ell/w` full blocks and **no per-piece tails**.
3. Build F_w once and evaluate it at all Q shifts. Product/remainder trees use `O~(w+Q+v)=O~(v+sqrt(v ell))` ring operations. When `v>ell`, the cap gives `w=ell,Q=v`; ignoring this cap would misprice short intervals.
4. Multiply the block values into their piece/record products. Restore `m_j^L_j` if exact products rather than gcd-equivalent unit multiples are wanted; this adds J modular exponentiations on O(log N)-bit exponents.

Summing by Cauchy--Schwarz over at most O(log N) length groups gives

```
C_product,bit = C_prog,bit + (J+sqrt V) poly(log N).         (7)
```

Assume record-count logarithms are polynomial in log N; otherwise include them explicitly. This is a constructive application of monic product/evaluation arithmetic, not an implicit-product oracle. Repeated shifts, overlapping intervals, and composite coefficients are allowed. Reversals of monic divisors have constant term 1, so remainder trees do not invert point differences. The only scalar inversions here are the gcd-checked m_j. No factorial quotient is used, so W015's H! precheck is unnecessary for this algorithm.

Take gcds of computed record products. If one is proper, return it. A full gcd is localized by bisecting **one** original interval and recomputing half-products using the single-interval method. A left unit directs descent right; a left full gcd directs descent left; a proper gcd stops. The sum of costs is `O~(sqrt L_j)` along the descent. Every original leaf is an integer strictly between 1 and N, hence cannot have gcd N. This proves recovery, including prime powers, within (7). A covered prime guarantees a nonunit record; without coverage the algorithm may legitimately find none.

This sharing is realized on an explicit paid varying-m family, not just named: take integers `R>=2`, `N>1+R(2R-1)`, and the R records

```
m_i=i,       T in [R,2R),       1<=i<=R.
```

Constructing records and checking slopes costs `O~(R)`; any nonunit slope immediately factors N. Otherwise compute all these products with the algorithm above. Here `J=R,V=R^2`, so shared work is `O~(R)`, versus `O~(R^(3/2))` for applying the separate square-root routine to every record. This is a proved saving in that specified product workload, not a claim about optimality, factor success on every N, or new prior art. Its union is not proved to cover a factor. Repetitions count honestly, and early factor discovery can shorten either algorithm. The construction therefore strengthens the comparator; it supplies no new N-only factoring improvement.

**Ceilings and break-even.** For `K>=1`, S as in (3),

```
max(K,S/B) <= G(B) <= K+S/B,
K+B+G(B) <= 2K+B+S/B.                                    (8)
```

Let h be a paid, usable upper choice of baby width (all widths up to h meet the component-order contract, or an earlier check factors N). Choose `B=min(h,ceil(sqrt S))`. The numerical list envelope is, within absolute constants,

```
K + sqrt S + S/h,                                         (9)
```

with the last term omitted when there is no binding cap. This is a statement about this explicit schedule, not a lower bound for factoring or all collision algorithms. At the target prime, h cannot be justified above the order bound (5) on the no-factor branch.

For a precise **normalized budget test**, let A denote the candidate's extra acquisition/degree/width work, after putting both algorithms in the same cost units and cancelling only identical progression acquisition. For a target budget R0, the actual ceiling-sensitive test is

```
A + K + B + sum_i ceil((2E_i+1)/B) < R0.                   (10)
```

With nonbinding order cap, a sufficient explicit inequality is

```
R0 > A+2K+1,
S < ((R0-A-2K-1)/2)^2,                                   (11)
```

since `ceil(sqrt S)+S/ceil(sqrt S) <= 2sqrt S+1`. With `h<sqrt S`, the sufficient inequality becomes

```
S < h(R0-A-2K-h),            R0>A+2K+h.                   (12)
```

These are exact inequalities for the stated normalized list budget, not wall-clock or leading-constant claims between soft-O bit bounds. An implementation comparison must insert its actual polynomial arithmetic, root, and acquisition costs. For asymptotic exponent comparisons, (9) provides the appropriate accounting.

Separate progression evaluation has envelope `P_sep=J+sum_j ceil(sqrt L_j)`. The stronger available envelope is `P_batch=J+ceil(sqrt V)`. In the common non-record-dominated regime `J=o(sqrt V)`, a power-saving certificate recipe therefore needs A and K below the sqrt(V) scale, S below the V scale, and, if capped, S/h below sqrt(V), by suitable powers after logarithmic costs. The weaker condition `S << (sum sqrt L_j)^2` can falsely suggest a gain already supplied by (7).

For a single progression split into K certificates, the comparator may merge the split pieces: use `J=1,V=L`, not an artificially fragmented comparator. For equal errors, `S=K(2E+1)`: both the K term and this whole error sum must fit the budget. Even E=0 costs at least one giant/tag per certificate. If the same coverage acquisition dominates both methods, a downstream saving need not improve their total bound.

**A constructive fixed-m certificate calculation.** This shows what genuine work can be saved *after matching the progression information*, while exposing the remaining gate. Suppose a supplied progression has a prime factor in `[X,2X)`, with `N` comparable to `X^2`. Let its t-length be L; use the nontrivial regime `L` comparable to `X/m`. No prime-factor knowledge is used to build the following coefficients.

For each t-block starting at a with width at most H, put `x0=1+ma`. Given integer `Q0>=1`, continued fractions of the public rational `-Nm/x0^2` produce integers `1<=q<=Q0,a1` with `|q(-Nm/x0^2)-a1|<=1/Q0`. Take a0 nearest `qN/x0`, and define `A(T)=a0+a1(T-a)`. The exact reciprocal remainder gives, for `u=T-a>=0`,

```
|A(T)-qN/(x0+mu)|
 <= 1/2 + H/Q0 + Q0*N*m^2*H^2/x0^3.                      (13)
```

Use the ceiling of the displayed public rational bound for E. Certificate generation and validation cost polynomial bit time per block; q, coefficients, endpoints and exponents have O(log N) bits in the regime below. The continued-fraction guarantee follows by taking the last convergent before denominator Q0 is exceeded (or the exact terminal convergent). This is an explicit coefficient algorithm, not a simultaneous-approximation existence oracle.

For `1<=m<=X^(1/3)`, choose rounded positive integers comparable to

```
H  = X^(3/5) m^(-4/5),
Q0 = X^(1/5) m^(-3/5).
```

Floor each at 1 and truncate the last block; the count is `K=ceil(L/H)`. The range ensures Q0 is at least constant and H is a legal nonempty width. Formula (13) yields

```
K = O(1+X^(2/5)m^(-1/5)),
E_i = O(1+X^(2/5)m^(-1/5)),
S = O((1+X^(2/5)m^(-1/5))^2).
```

Choose B of the same scale, subject to the paid order contract. All ceiling/record terms are included. Hence the complete **conditional** certificate-and-search cost is

```
C_prog,bit + C_base,bit + O~(1+N^(1/5)m^(-1/5)).           (14)
```

Its search term is smaller than the same progression's `O~(N^(1/4)m^(-1/2))` envelope by a power when `m<N^(1/6)` by a fixed power, and ties at the boundary. For larger m the assumed Q0 balance falls below 1, so this derivation cannot be extrapolated. These are optimizations of a sufficient constructive recipe, not optimality or impossibility claims. In particular, the favorable slope/error representation does save conditional downstream work; it would be too strong to assert that *all* savings are only extra residue information.

There is a **paid randomized completion** of (14), so it would also be too strong to leave every acquisition route unresolved. Set `t_min=max(1,ceil((X-1)/m))`, and choose

```
W = max(1,ceil(X^(2/5)m^(-1/5))),
B = max(1,min(W,floor(sqrt(t_min)))).
```

The regime above gives `B=Theta(W)` and `B^2<=t_min<=t` (small constant-size cases may be handled directly). Draw a uniformly random integer `a in [1,N-1]` and compute `gcd(a,N)`. A nonunit a gives a proper factor. Conditional on being a unit, its reduction modulo the promised p is uniform in the cyclic group of size p-1: reduction from the unit group modulo N is surjective with equal fibers. Its m-th power is therefore uniform in the cyclic subgroup of size `t=(p-1)/m`. The number of elements in that subgroup of order below B is

```
sum_(d|t, d<B) phi(d) <= sum_(d=1)^(B-1) d
                       = B(B-1)/2.
```

Thus the chance of order below B is at most `B(B-1)/(2t)<=1/2`. Test the B powers of `beta=a^m` as specified earlier. A proper gcd finishes; all unit checks validate every prime component; a global ORDER-FAIL can occur only if the order at this promised p is below B. Consequently each independent attempt returns a factor or a usable base with probability at least 1/2. Repeating only global failures takes at most two attempts in expectation, each costing `O~(B)` bit operations, including modular powering and all gcds. Exact uniform sampling by binary rejection has O(log N) expected bit cost per draw. This proves an always-correct **expected-time** primitive, not deterministic worst-case time or a worst-case random-bit bound.

Combining it with the explicit coefficients and collision consumer gives

```
E[total bit cost | supplied balanced progression promise]
    = C_prog,bit + O~(1+N^(1/5)m^(-1/5)),
       1<=m<=N^(1/6) up to the fixed balanced-range constants.  (15)
```

Here `C_prog` is only reading the supplied information when it is the primitive's input; it becomes actual acquisition/coverage work for any N-only application. The theorem is a constructed promise-family upper bound using known machinery; novelty relative to all residue-class algorithms has not been investigated or claimed. It proves no improved complete general factoring bound.

The same random-order argument works for common `beta=a^M` if one has a *paid guarantee* that some covered prime's M-th-power image has size at least `B^2`. That size is `(p-1)/gcd(p-1,M)`. A sufficient lower bound from `p>=X` is `(X-1)/M`, often useless for a large lcm; exponent bit cost log M also remains. Thus the fixed-m completion does not silently solve the varying-m order/coverage problem.

For the deterministic comparison, a paid alpha with `ord_N(alpha)>mB` suffices. Harvey's Proposition 2.7 obtains order `>D`, a factor, or a primality conclusion for `N^(2/5)<=D<=N` in `O~(sqrt D)` bit time. Set `D=max(ceil(N^(2/5)),mB)`: in this regime its cost is `O~(N^(1/5))`, erasing the m power saving. This is a sufficient fallback, not a lower bound. [Primary statement](https://arxiv.org/html/2010.05450#S2.SS4)

For a concrete next computation toward the lab's deterministic target, fix `X~N^(1/2), m~N^(1/10)`. Then `L~N^(2/5)`, `H~N^(11/50)`, `Q0~N^(1/25)`, and `K,E,B~N^(9/50)`; the product costs N^(1/5) scale. Analyze the **specified deterministic** attempt list `a=2,3,...,A+1` with `A+1<N`: gcd-test a, form `a^m`, and check its first B powers. Derive an explicit bound on A, or a paid recovery from all global small-order failures, which fits total budget `O~(N^(9/50))`. Merely extrapolating the random success proof to this list is invalid. This is the remaining deterministic computation, not an empirical parameter-search request. If expected time is the chosen target, base acquisition is already paid by (15); the next gate is instead an explicit N-only covering family with its records, total progression length, errors, and common-base image-size bound meeting (7)-(12). No such family is supplied in W016.

**Primary-art relation and the unsupported premise.** The comparator is a specialization of the classical block-product method. Harvey's Section 2.3 states its square-root interval cost, and Sections 2.2 and 4 describe product trees, batched collisions, and global-match handling. His linear-combination search already shares work across certificates. The present consumer is not a new invention of that search machinery; (1) is the audited sparse-coordinate representation feeding it. [Harvey, primary paper](https://arxiv.org/html/2010.05450)

Supplied `p=1 mod m` is exactly residue-class factoring information with residue 1. It does not follow from knowing N. Nor is the square-root product always the best algorithm once such information is supplied: Lenstra's 1984 opening theorem finds all divisors in a specified class `r mod m`, `gcd(r,m)=1`, in polynomial bit time when `N^(1/3)<m<N`. Residue 1 satisfies its coprimality condition. No claim of optimality for (7), or comprehensive comparison with later residue methods, is made. [Lenstra, primary paper, p.331](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1984b/art.pdf)

The exact relation to p-1 methods is order annihilation. Raising alpha to m kills part of the order, and the remaining order divides t. In conventional stage one, a constructed smooth prime-power exponent M aims to contain p-1; stage two tests residual prime possibilities after that powering. Montgomery--Silverman explicitly describe both stages and fast two-list collision operations. [Primary paper, pp.839-841](https://cr.yp.to/bib/1990/montgomery.pdf) W016 does not require m to be smooth or t to be prime. Its target is the reciprocal-approximation error D-e, not simply the remaining prime in p-1. Thus the precise relationship is a common powered-order/collision primitive with a different conditional error representation; calling all of W016 literally ordinary stage two would overstate equivalence. Stage-one success or favorable residual order is not an automatic consequence of the progression promise.

The missing N-only premise is an algorithm which, from N alone, either returns a factor or constructs the finite progression/certificate family, proves that it covers at least one prime factor, obtains usable bases or resolves order failures, and does all of this within the improved full budget. Large m, small L, small E, short common-base exponent and sufficient component order cannot all be granted as uncharged advice. If a target has `p-1=2r` with r prime, its divisors are `1,2,r,2r`; listing divisors of an unrelated public smooth exponent cannot guarantee a useful large m. This observation needs no assertion that infinitely many such primes exist and proves no all-algorithm obstruction. Small m=1 (or m=2 for odd factors) supplies easy coverage but no new large-modulus information.

**Disposition and delivery.** Accept (1), nonzero recovery (2), the degree-independent power m under integer-coefficient guards, the matched single-progression comparator, the conditional consumer (4), and the explicit common-base construction with loss (5). Add the stronger family comparator (7), cap/ceiling inequalities (8)-(12), and the constructive linear calculation (13)-(14), and the randomized acquisition/completed promise bound (15), all with the stated scope. Reject a new complete factoring bound, free progression coverage, free high powered order, unqualified sharing across unrelated bases, and novelty/optimality/lower-bound claims. The derived product-family saving is a conditional workload result; (15) pays random base acquisition but retains the supplied factor-progression promise. Finite factoring evidence: **none run or claimed**. Complete new factoring improvement: **NONE**.

All delivered files are inventoried in [delivery-manifest.json](W016-progression-review-evidence/delivery-manifest.json), with SHA-256 and byte lengths. [delivery.sha256](W016-progression-review-evidence/delivery.sha256) also covers that manifest; it excludes itself to avoid self-reference. The final response supplies its independent hash. [integrity-check.json](W016-progression-review-evidence/integrity-check.json) checks frozen input bytes and records live-source drift. Hash correctness is evidence integrity, not mathematical proof. No shared implementation changed, so no solver/Lean test run was needed or represented as performed.
