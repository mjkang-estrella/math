# W030 review: shared roots, uncarried representatives, and the actual consumer

2026-10-08 local / 2026-10-09 UTC. **Accept the smaller representation and its exact product identity, with the implementation and scope completions below. No faster aggregate consumer is established. Verified complete factoring improvement: NONE.** The representation removes pairwise root acquisition and the old polynomial-chart height inflation. Using the established explicit-anchor consumer still pays for the pair records and retains its one-fifth cost envelope. No counterexample to the correctly scoped representation was found. The dense-box and literal subset attempts do not establish a fixed-power improvement; their costs are not lower bounds on other product algorithms.

The reviewed parent construction is the frozen `research/hypotheses/W030.md`, SHA-256 `d1f5ee7be46e8a5107f49f1d414fa4b90a37375961e8343405c7a49f2262e7d0`. The [full brief](W030-uncarried-root-review-evidence/full-brief.txt), [input manifest](W030-uncarried-root-review-evidence/input-manifest.json), and [method/read scope](W030-uncarried-root-review-evidence/method-and-read-scope.json) delimit this review. W022's primitive valuation cover, W024's public prime schedule and residue filter, and W020's arbitrary nonzero-exponent recovery are accepted interfaces, not new audits. W025's explicit-anchor consumer is the comparator. W029 is excluded. The parent continues constructive work independently.

**1. Domain and imported coverage.** Write the original auxiliary modulus as $M=\ell^k$, where $\ell\ge3$ is prime, $\gcd(\ell,N)=1$, and $k\ge1$. The imported cover uses $2\le U<M$, $V=\lceil M/U\rceil<M$, positive $u$, and signed nonzero $v$. For a covered pair the two weight valuations coincide. At valuation $s$, put

\[
r=\ell^s,\quad m_s=M/r,\quad Q_s=m_s^2=\ell^{L_s},\quad L_s=2(k-s),
\]
\[
U_s=\lfloor U/r\rfloor,\quad V_s=\lfloor V/r\rfloor,
\quad W_s=\lceil W/r\rceil.
\]

Enumerate $0\le s\le\lfloor\log_\ell\min(U,V)\rfloor\le k-1$ by integer comparisons. The primitive domains are $1\le u\le U_s$, $1\le|v|\le V_s$, with $\ell\nmid uv$. They contain every divided witness, for which

\[
S=up+vq,\quad |S|\le W_s,\quad
S^2\equiv4Nuv\pmod{Q_s},\quad m_s\mid up-vq.
\]

Here $N=pq$, $p$ is prime, and $q$ need not be prime. The new representation is used separately at each stratum. In particular it cannot omit positive valuations, use the original unstripped weights in the filter, or silently reuse the top-stratum carry bound. There is no modulus-one branch: $L_s\ge2$. The root-table algebra also works for $L\ge1$ and signed unit $u$, but those observations do not extend the imported covering theorem to other rectangles.

In the rest of the local derivation, suppress $s$. Use $U,V$ as bounds on coordinate magnitudes and write $U_c,V_c$ for actual numbers of enumerated coordinate occurrences. In the inherited signed rectangle, $U_c\le U$ and $V_c\le2V$; this constant does not change the parent's asymptotic notation. Empty coordinate lists or class intersections give the empty product $1$. Singleton lists require no special root assumption. Zero weights are absent because they are not units. Negative weights use their mathematical residues modulo the positive modulus; there is no square-root operation on negative real numbers.

**2. Two tables cover precisely the rooted pairs.** Let $\chi$ be the square character on nonzero residues modulo $\ell$. Choose a nonzero nonsquare $\delta$ modulo $\ell$, lift it as an integer, and compute its inverse modulo $Q$. Assign a column $v$ to the unique $\epsilon\in\{0,1\}$ with $\chi(v)=(-1)^\epsilon$. A row belongs to this class exactly when $\chi(Nu)=(-1)^\epsilon$. Thus

\[
\chi(4N\delta^\epsilon u)=1,\qquad
\chi(\delta^{-\epsilon}v)=1.
\]

Conversely, $4Nuv$ is square exactly when these two class labels agree. In each nonempty matching class, select and lift one root per coordinate:

\[
A_u^2\equiv4N\delta^\epsilon u,\quad
B_v^2\equiv\delta^{-\epsilon}v\pmod Q,\quad 0\le A_u,B_v<Q.
\]

Both roots are units. Their product squares to $4Nuv$; over an odd prime power its two roots are precisely $A_uB_v$ and $-A_uB_v$ modulo $Q$. They are distinct because $2A_uB_v$ is a unit. Changing a selected coordinate-root sign only relabels the two pair signs. It is unnecessary to store both coordinate signs and then four pair sign combinations.

There are two class families, not two copies of every coordinate: each unit row belongs to exactly one class and each unit column to exactly one class. A class lacking a partner list can be skipped. Acquisition can therefore use at most $U_c+V_c$ lifts, with a constant-factor bound still valid for a less careful implementation. This is a real reduction relative to explicitly acquiring/storing one root per pair; it is not a claim that all older chart acquisition had required independent pairwise lifting.

The roots are constructible without any square-root oracle modulo $N$. For example, build the small table $x\mapsto x^2\bmod\ell$, retain one root for each nonzero square, and select a nonsquare from the complement. This costs $O(\ell)$ small modular operations and storage. Reduce each radicand modulo $Q$, look up an initial root modulo $\ell$, and use the inherited digit lift

\[
a_{j+1}=a_j+\ell^j d_j,\qquad
d_j\equiv\frac{D-a_j^2}{\ell^j}(2a_j)^{-1}\pmod\ell.
\]

The division is exact, and $2a_j$ is invertible modulo $\ell$. There are $L-1$ lifts and $O(L)$ digit-extraction steps per entry. Inverses, reductions, radicand construction, coordinate enumeration, and the small table are paid. Brute-force root trials per entry are also a valid slower implementation, with their factor $\ell$ charged. No pair array is needed for any of this.

**3. Exact uncarried identity, height, and signed carries.** Expand each chosen representative in base $\ell$: $A_u=\sum_i a_{ui}\ell^i$, $B_v=\sum_j b_{vj}\ell^j$, with $0\le i,j<L$ and digits in $0,\ldots,\ell-1$. Define the ordinary integer

\[
R(u,v)=\sum_{i+j<L}a_{ui}b_{vj}\ell^{i+j}.
\]

Every omitted term of $A_uB_v$ contains $\ell^L=Q$, so $R\equiv A_uB_v\pmod Q$. No carry propagation or pointwise reduction is needed for this identity. The coefficient bound gives

\[
0\le R\le(\ell-1)^2\sum_{k=0}^{L-1}(k+1)\ell^k
\le L(\ell-1)(Q-1)<L(\ell-1)Q.
\]

As a symbolic check of the endpoint, the first upper bound equals

\[
\bigl(L(\ell-1)-1\bigr)Q+1.
\]

The looser bound used by W030 is valid. Set $c=L(\ell-1)$, $H=\lceil W/Q\rceil+c$, and $T=2H+1$. For a covered $S$, precisely one sign $\sigma\in\{+1,-1\}$ obeys $S\equiv\sigma R\pmod Q$, and

\[
\tau=(S-\sigma R)/Q\in\mathbb Z,\qquad |\tau|\le H.
\]

Both signs have the common inclusive interval $[-H,H]$. This intentionally includes lifts outside $[-W,W]$; it is a covering superset, not equality with the bounded-$S$ set. If exact pointwise endpoints were desired, they would be

\[
\left\lceil\frac{-W-\sigma R}{Q}\right\rceil
\le\tau\le
\left\lfloor\frac{W-\sigma R}{Q}\right\rfloor,
\]

with an empty interval when the endpoints cross. Computing those endpoints for every pair would reintroduce pair work and is unnecessary here. All divisions use mathematical floor/ceiling, including negative numerators. Descendant carry intervals may be empty or singleton; their products and decoding use the usual conventions.

The leaf exponent is the actual signed integer

\[
E=u+Nv-\sigma R-Q\tau.
\]

It is not reduced modulo $Q$, $N$, or an unknown order. For all represented leaves,

\[
|\sigma R+Q\tau|\le W+(2c+1)Q,\qquad
|E|\le U+NV+W+(2c+1)Q.
\]

Thus the bit-width assertion is sound after adding $1$ inside logarithms to cover zero-size bounds. Inherited polynomially bounded $M,W$, together with W024's polynomial-in-bitlength $\ell$, give $O(\log N)$-bit exponents and intermediate integers. Squaring an $O(\log Q)$-bit lifting operand only changes that width by a constant factor. Storing both the root integer and its digits costs $O(L\log\ell+\log(U+V+1))$ bits per entry, not constant bits per entry. Short exponents do not make the number of leaves free.

**4. The low-digit filter works on whole Cartesian blocks.** Within one class, group rows by $a=a_{u0}\ne0$ and columns by $b=b_{v0}\ne0$. These labels determine the original coordinate residues:

\[
u\equiv (4N\delta^\epsilon)^{-1}a^2,\qquad
v\equiv\delta^\epsilon b^2\pmod\ell.
\]

Consequently each class/group/sign block has the constant residue

\[
e_{\epsilon,a,b,\sigma}
=(4N\delta^\epsilon)^{-1}a^2+N\delta^\epsilon b^2-\sigma ab
\pmod\ell.
\]

Keep precisely the blocks with nonzero residue. The $-Q\tau$ term vanishes modulo $\ell$, so **every** retained exponent is nonzero, including padded carries. Both signs cannot vanish because their difference is $2ab$, a unit; nevertheless survival of some sign alone would not prove survival of the true witness.

For that witness, the imported identity applies unchanged:

\[
E=u+Nv-S=(p-1)(vq-u)\equiv u(p-1)^2\pmod\ell.
\]

The true leaf survives exactly when $p\not\equiv1\pmod\ell$. W024's complete public schedule supplies such a legal base, or already finds a factor by a prime gcd. In particular $p\equiv-1$ must retain the actual sign even when the opposite sign is discarded. No assumption about the integer sign of $E$, or about $\gcd(E,N)$, is needed.

There are at most $4(\ell-1)^2$ class/group/sign labels before skipping empty blocks. Charge these tests and labels, not $UV$ tests. Put each coordinate occurrence into its bucket once; a block stores two bucket references and its sign. Recopying a whole table for every partner could cost $O(\ell(U_c+V_c))$, still polynomial logarithmic for this schedule but unnecessary and inconsistent with an unqualified linear-entry claim. Index sharing achieves the stated smaller representation. Equal residues, equal numerical exponents, and repeated tags across bases/ranges/strata do not justify discarding occurrences from an already frozen product.

**5. All strata, acquisition cost, and localization.** The inherited coordinate counts satisfy

\[
\sum_s(U_s+2V_s)=O(U+V).
\]

Root precision is at most $2k$; even independently rebuilding lower-stratum tables therefore preserves $O(U+V)$ entries times paid logarithmic work. Charge an additional $O(k\ell^2)$ block-label budget per base/range, and small-prime preprocessing per base if shared. A conservative concrete local bit envelope, with

\[
B=1+\lceil\log_2(N+1)\rceil+\lceil\log_2(M+1)\rceil
+\lceil\log_2(W+1)\rceil+\lceil\log_2(\ell+1)\rceil,
\]

is $O((1+k)(1+\ell^2+U+V)B^3)$ using schoolbook arithmetic. This deliberately loose upper bound pays for enumeration, lifting, integer division, inverses, digits, buckets, and labels; it hides no $UV$ table. A direct storage bound is $O((U+V+k\ell^2+k)B)$ bits. Rebuilding across public ranges or storing several bases adds their actual budgets. W024 supplies at most $n=\operatorname{bitlen}(N)$ primes with $\ell\le16(n+1)^2$, so these factors are polynomial in $n$, not constants. An exponential dependence on $\ell$ or $L$ would not inherit that conclusion.

The carry bound in stratum $s$ is

\[
T_s=O\left(1+\frac{Wr}{M^2}+\ell(k-s)\right),\qquad r=\ell^s.
\]

With $P_s\le2UV/r^2=O(M/r^2)$ primitive signed pairs, the total number of represented sign/pair/carry occurrences is bounded by

\[
\sum_s 2P_sT_s
=O\left((1+\ell k)M+\frac WM\right).
\]

This is a useful improvement over the old quartic-chart height envelope and, up to logarithmic factors, matches the canonical-root occurrence envelope. It is a size bound for an implicitly represented family, not the time to compute its product. The new padding defines a new public family with the required witness coverage; this does not assert equality with the entire old padded chart product. Choose the new family before the trial and preserve its own product during localization.

All roots, digits, classes, buckets, signs, carry intervals, and occurrence tags are public and independent of $\alpha$. Freeze them before a trial. A product-preserving restriction splits the block list, a bucket's ordered occurrence list, or a carry interval into disjoint pieces. Empty products are $1$; singleton decoding computes the original $u,v,\tau,E$. This uses list slices/index ranges, not a claim that low-digit buckets are consecutive integer intervals. A balanced restriction tree has depth $O(1+\log(1+\#\text{blocks})+\log(1+U_c)+\log(1+V_c)+\log T)$, with the public schedule's label depth also paid.

Do not change a root sign, choose a new representative, trim a carry interval, deduplicate exponents, or reacquire a cheaper family during localization. Those changes need not preserve the detected product. W020's accepted expected-at-most-two-trial theorem applies only after a finite correct evaluator/localizer supplies a leaf and its nonzero integer exponent, using the **original uniform** $\alpha\in\{1,\ldots,N-1\}$. A nonunit initial gcd already splits $N$; signed powering on the unit branch uses its checked inverse. Even inputs and exact prime powers retain the imported polynomial-bit preprocessing. The complete trial covers every public base and factor range; one possibly uncovered block or base is not a trial. No restriction cost, leaf decoding cost, or repeated evaluator call is supplied for free by this representation.

**6. Explicit column setup and exact polynomial evaluation.** The column claim can be realized without a hidden $VL^2$ powering loop. Define the public integer features

\[
D_i(v)=\sum_{j<L-i}\ell^{i+j}b_{vj}
=\ell^i(B_v\bmod\ell^{L-i}).
\]

They satisfy

\[
D_0(v)=B_v,\qquad
D_{i+1}(v)=\ell D_i(v)-Qb_{v,L-1-i}\quad(0\le i<L-1).
\]

Hence they can be stored or generated in $O(V_cL)$ integer operations on $O(\log Q+\log\ell)$-bit operands. Each $0\le D_i<Q$, and

\[
R(u,v)=\sum_i a_{ui}D_i(v).
\]

This also evaluates a supplied pair in $O(L)$ small-digit multiplications and additions after column setup. It improves a logarithmic implementation factor only; evaluating every pair still pays $U_cV_c$. Storing all these integer features adds $O(V_cLB)$ bits beyond the root/digit representation; generating one column at a time uses $O(LB)$ working bits instead. Caching every modular coordinate below similarly adds $O(V_cL\log N)$ bits. None of those optional caches is part of the smaller representation's storage bound above.

For fixed sign put $\beta=\alpha^Q$ and $X_i(v)=\alpha^{-\sigma D_i(v)}$. Their recurrence is

\[
X_{i+1}(v)=X_i(v)^\ell\,\beta^{\sigma b_{v,L-1-i}}.
\]

Obtain $X_0(v)=\alpha^{-\sigma B_v}$ by base-$\ell$ Horner powering through the $L$ digits; precompute the $O(\ell)$ powers of $\alpha^{-\sigma}$ and $\beta^\sigma$ if desired. Computing $\beta$ takes $O(L\log\ell)$ modular multiplications, or ordinary binary powering. Horner setup and the recurrence take $O(V_cL)$ powers with exponent at most $\ell$, hence $O(V_cL\log\ell)$ modular multiplications, plus the optional $O(\ell)$ tables. Both signs cost at most a constant factor. There is no extraction of an $\ell$-th root modulo $N$.

For a block $I$ of $b$ rows and a fixed retained column group/sign, the actual polynomial over $\mathbb Z/N\mathbb Z$ is

\[
F_I(Y,X_0,\ldots,X_{L-1})
=\prod_{u\in I}\left(1-\alpha^uY\prod_iX_i^{a_{ui}}\right).
\]

Substituting $X_i=X_i(v)$ and $Y=\alpha^{Nv-Q\tau}$ gives exactly

\[
F_I\bigl(\alpha^{Nv-Q\tau},X(v)\bigr)
=\prod_{u\in I}\left(1-\alpha^{u+Nv-\sigma R(u,v)-Q\tau}\right).
\]

This is equality modulo $N$, including negative $u,v,\tau$, repeated modular values, and composite $N$; only the unit $\alpha$ is inverted. For $b=0$, both sides are $1$. It is the required row-block product, not an approximate norm or a pointwise oracle.

Charge row powers $\alpha^u$ and column powers $\alpha^{Nv}$ separately. Their usual binary-power setup is polynomial logarithmic per entry. Carry factors form the progression $(\alpha^{-Q})^\tau$, with a signed binary-power starting value and ordinary successive multiplications. Separate column and carry factors may be stored compactly, but emitting every $Y(v,\tau)$ still costs $V_cT$. The $O(V_cL)$ coordinate setup does not include all polynomial evaluations at column/carry pairs.

**7. What the attempted consumers actually cost.** Expanding $b$ factors into the full dense bounding box allocates

\[
D_b=(b+1)\bigl((\ell-1)b+1\bigr)^L
\]

coefficient slots. Each coordinate degree is at most $b(\ell-1)$, and the $Y$-degree is at most $b$. The actual support may occupy far fewer slots. For this full-box allocation the cost is real: already $b=1$ allocates $2\ell^L=2Q$ slots although the polynomial has only two terms. When $M=N^m$, $m>0$, $Q=M^2$, and $b=N^\eta$, $\eta>0$, the logarithm of this box size is at least a constant multiple of $(\log N)^2/\log\ell$; with the allowed $\ell=\operatorname{poly}(\log N)$, that is superpolynomial in $N$. A generic dense construction at those degrees cannot yield the target saving. This conclusion concerns allocating this box, not a lower bound from the polynomial's degree alone.

The subset formula is

\[
F_I=\sum_{J\subseteq I}(-1)^{|J|}\alpha^{\sum_{u\in J}u}
Y^{|J|}\prod_iX_i^{\sum_{u\in J}a_{ui}}.
\]

Literal enumeration makes $2^b$ subset visits even when terms later merge or cancel. Keeping that implementation polynomial in $N$ requires $b=O(\log N)$; reducing the number of row blocks from $U_c$ to $U_c/b$ then gives at most a logarithmic saving. Each exponent vector has $O((L+1)\log(1+\ell b))$ bits and each modular coefficient has $O(\log N)$ bits. Building, merging, storing, and evaluating those terms are additional paid operations. No fast multivariate multipoint routine follows from writing the subset sum.

**Wording correction:** the inequality “support at most $2^b$” alone does not imply that every compact construction requires $b=O(\log N)$. That restriction applies to literal subset enumeration, or to a proved comparable worst-case expansion, not to all possible merged-support/circuit algorithms on these root tables. Likewise, the dense-box upper bound does not prove the support fills its box. W030 should qualify its “only permits” sentence accordingly. No particular compact consumer with the required stronger cost is supplied by this review.

The coefficient matrix $C_{ij}=\ell^{i+j}\mathbf1_{i+j<L}$ has determinant

\[
\det C=(-1)^{L(L-1)/2}\ell^{L(L-1)}\ne0
\]

over the rational field $\mathbb Q$. Reversing its columns makes it triangular with diagonal $\ell^{L-1}$. Thus an identity representing this bilinear form on arbitrary digit vectors as a sum of products of linear features needs at least $L$ such features. This is a linear-algebra statement. It neither rules out nonlinear encodings or aggregation, nor gives a product-circuit lower bound, nor says the actual restricted root tables realize arbitrary vectors. It also does not assert rank $L$ over the ring modulo the auxiliary $Q=\ell^L$.

**8. Comparator, conditional arithmetic, and remaining work.** Feed the filtered anchors to the accepted W025 consumer, grouping equal strides $Q_s$. Its cost remains

\[
\widetilde O(K+\sqrt{KT}),
\]

including explicit anchor generation, babies/giants, monic product and remainder trees, tags, and localization. New root acquisition avoids $UV$ lifts, but constructing the anchors still evaluates the pair interaction once per retained record. Sharing column features makes that work polynomial logarithmic per pair, not sublinear in their number. The filter provides no general sublinear anchor-count guarantee.

For balanced top-stratum bookkeeping, $U,V\asymp\sqrt M$, $W\asymp\sqrt{NM}$, and

\[
T=O\left(1+\frac{\sqrt N}{M^{3/2}}+\ell\log_\ell M\right).
\]

With the $K=O(M)$ explicit-anchor envelope, this remains

\[
\widetilde O\left(M+N^{1/4}M^{-1/4}\right),
\]

balanced at $M=N^{1/5}$. Summing the new stratum envelopes gives the same cost up to logarithmic factors: $\sum_sK_s=O(M)$ and

\[
\sum_s\sqrt{K_sT_s}
=O\left(\sqrt{(1+\ell k)M}+\sqrt{W/M}\right).
\]

This is a bound on the established explicit implementation, not an optimality theorem. Public prime/range schedules, rounded targets, W024's $k=1$ handling and paid width fallback, the small-factor screen, and W020's preprocessing/restart costs remain part of any complete composition.

If an actual aggregate consumer cost $\widetilde O(U+V+\sqrt{UVT})$ were proved, balanced substitution would instead compare $\sqrt M$ with $N^{1/4}M^{-1/4}$, giving $M=N^{1/3}$ and exponent $1/6$. **That implication is bookkeeping, not an algorithm.** Even it does not pay for unbalanced ranges, where $U+V$ can be $\Theta(M)$. Neither rank nor failed expansions proves such a consumer impossible.

The accepted deliverable is therefore: deterministic small-table acquisition; exact square-class and signed-root coverage in every inherited primitive stratum; an uncarried integer representative with logarithmic carry inflation; a whole-block nonzero filter preserving the scheduled witness; bounded bit widths and product-preserving frozen restrictions; and an explicit $O(V_cL)$ column recurrence with the exact row-polynomial identity. The revised claim is the limited cost conclusion for literal dense/subset constructions. The unresolved object is a uniform aggregate evaluator over these supplied digit lists that supports the necessary restrictions and singleton decoding at its claimed cost, followed by a complete all-range cost composition. A divide-and-conquer, norm, or other computation that actually avoids both pair records and subset expansion could change the verdict; another certificate of the root identity would not.

This was a symbolic audit. No numerical certificate, parameter sweep, prior-certificate rerun, solver execution, Lean build, installation, commit, or delegation occurred. No prior-art search was needed for these algebraic and implementation claims; no novelty claim is made. Only this report and its assigned evidence directory were written. The [verification record](W030-uncarried-root-review-evidence/verification.json) and [delivery manifest](W030-uncarried-root-review-evidence/delivery-manifest.json) record the final hashes and boundary. All mathematical findings concern the frozen inputs, not concurrent parent edits.
