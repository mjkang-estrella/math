# W019 Part A: independent public-cover review

2026-10-08 local / 2026-10-09 UTC. **Accept A1–A6 with explicit integer boundaries and an expected-time qualification. Accept A7 as a square-root acquisition identity, not as an implicit collision algorithm. Verified new complete factoring improvement: NONE.**

The construction supplies an N-only cover, unlike the supplied-progression premise of W016. With the completions below, it gives a classical Las Vegas splitter with expected `N^(1/5) poly(log N)` bit cost. This recovers a known numerical exponent using known search machinery. It is neither a deterministic-bound improvement nor a novelty claim. The modular stationary weighted-sum mechanism has a particularly close antecedent in Harvey–Hittmeir, Proposition 3.3.

**Frozen scope.** This review concerns only A1–A7 of the complete, 221-line W019 snapshot, SHA-256 `afea2b58f83e36801e8630bfac5ed787f29801c4f589914aeaa04fb29e6f40df`. All of W019 was read; B/C receive no verdict here. The [complete brief](W019-public-cover-review-evidence/brief.txt), [input manifest](W019-public-cover-review-evidence/input-manifest.json), frozen local files, and [primary-source read scope](W019-public-cover-review-evidence/primary-sources/read-scope.json) are retained. STATE was consulted only for context at the recorded lines. W018's actual powered-base review and W013's consumer, independent review, and disposition were read, as was W016's review. W014 C-r2 is not an authority; no W008 lower-bound analogy is imported. The parent remains principal researcher.

**A1: the signed rectangle is a valid cover.** Let m be an odd prime, `gcd(m,N)=1`, `N=pq` with p prime, and let `1<=U<m`, `V=ceil(m/U)<m`. Primality of q is unnecessary. Put `z=p*q^(-1) mod m`. The `U+1` residues `jz`, `0<=j<=U`, are distinct: their equality would force a nonzero difference of indices smaller than m to vanish modulo m. Sort their representatives in `[0,m-1]`. Their U consecutive gaps have sum at most `m-1`, so one gap d satisfies

```
1 <= d <= floor((m-1)/U) <= V.
```

If its corresponding difference of indices is h, then `h z = d mod m`, with `0<|h|<=U`. Choose `u=|h|` and `v=sign(h)*d`. This gives `up-vq=0 mod m`, `1<=u<=U`, and `1<=|v|<=V`. These hidden-factor residues are used only in the existence proof. Enumerating the public `2UV` signed pairs requires no knowledge of z.

The sign is essential. For `z=-1 mod m`, a positive solution would require `u+v=m` or a larger multiple of m; none exists when `U+V<m`. Allowing `v=-u` resolves this obstruction. No distribution assumption on z is used. The hypotheses imply `U>=2`; `U=1` would give `V=m`, outside the contract. Also,

```
m <= UV < m+U < 2m.
```

Thus the explicit pair loop is Theta(m), even if it rejects many pairs later.

**A2: roots modulo m² and acquisition.** For a covered pair, with `S=up+vq`, the integer identity

```
S² - 4uvN = (up-vq)²
```

proves `S²=4uvN mod m²`, including negative v and negative S. Since m is odd and does not divide uvN, the radicand is a unit. It has either no roots or exactly two roots modulo m. Each is simple and lifts uniquely; hence it has either no roots or exactly two roots modulo m². If a root a of an integer representative R is known modulo m, compute

```
h = ((R-a²)/m) * (2a)^(-1) mod m,
s = a + mh mod m².
```

The division in the first expression is exact before reduction. Its sign is correct. The second root is `-s mod m²`, distinct from s. For A7, inverses in radicands must be taken modulo m², not merely modulo m followed by an arbitrary lift.

The exclusions `U<m`, `|v|<m` do real work. Allowing a coefficient to vanish modulo m invalidates the simple-root argument: a radicand of valuation one has no root modulo m², while zero modulo m² has m roots. Those branches cannot be treated as “zero or two simple roots.” Zero coefficients are not in this cover. A coefficient sharing a factor with N does not invalidate the integer recovery proof; an optional gcd with N can only give an earlier verified factor.

A sieve through a constant multiple of the desired m acquires and certifies the public prime in `O~(m)` work and storage. Check `gcd(m,N)` before inverses; with `m<N` a nonunit gcd is proper. No factor of N is supplied as advice. For a known odd prime, uniform sampling from `{1,...,m-1}` and Euler's criterion finds a nonresidue in expected two accepted draws. Charge exact binary rejection sampling and every rejected draw. One nonresidue can be reused in all Tonelli–Shanks calls. Writing `m-1=2^e d` with d odd is sufficient; full factorization of m−1 is unnecessary. These give expected polylogarithmic work per root acquisition. Alternatively, finding a nonresidue by a complete deterministic scan costs `O~(m)`, which fits A6's existing record budget. This alternative does not derandomize the W018 base step.

**A3: an explicit dyadic and integer completion.** Here is one choice of constants; it is not a tuned algorithm. Assume `m>=5` and consider integer left endpoints X with

```
4 sqrt(N/m) <= X <= sqrt(N).
R = sqrt(mN)/X,
U = ceil(R),
V = ceil(m/U),
W = ceil(2UX + VN/X).
```

All ceilings involving square roots can be computed by exact integer comparisons, without floating point. Since `sqrt(m)<=R<=m/4`, we have `U>=2` and `U<=m/4+1<m`; also `V<=ceil(m/2)<m`. Moreover,

```
2UX + VN/X <= 3 sqrt(mN) + 2X + N/X,
W <= 6 sqrt(mN)                         (N>1, m>=5).
```

For `p in [X,2X)` and `q=N/p`, the triangle inequality gives `|up+vq|<=W`. The last dyadic interval can be truncated at `floor(sqrt(N))`, inclusively. Including an endpoint twice would also be harmless if its tags were paid, but half-open intervals give a cleaner enumeration.

For each retained root representative `0<=s<m²`, construct exactly

```
a_s = ceil((-W-s)/m²),
b_s = floor((W-s)/m²),
ell_s = max(0,b_s-a_s+1).
```

Use mathematical floor/ceiling for negative numerators. Negative a_s, zero indices, empty intervals, and a singleton interval are legal. Do not truncate negative indices toward zero. Let K count all root records before discarding empty intervals and let `T=sum ell_s`, counting repeated occurrences. There are `2UV` pairs, at most two roots per pair, and therefore

```
K <= 4UV < 8m,
ell_s <= 1 + 2W/m²,
T <= K(1+2W/m²) < 8m + 16W/m
  <= 8m + 96 sqrt(N/m).
```

These inequalities justify A3 with the additive record/ceiling term. Repeated radicands or roots do not license deleting the associated coefficient tags. T counts a candidate once per progression occurrence; it is not an uncharged deduplicated union size.

**A4–A5: transfer and safe global-match recovery.** Handle even inputs and perfect powers first. On the remaining branch use the accepted W018 theorem with `M=m²` to obtain a verified factor, or a unit alpha and `beta=alpha^(m²)` with `ord_N(beta)>B`. The expected acquisition cost is `O~((log m+sqrt(B)+1) poly(log N))`. The uniformly sampled variable is alpha itself (W018's a), the preimage of beta, rather than beta sampled only from the power image. No deterministic stopping-time claim follows.

For `1<=j<B`, a nonunit `beta^j-1` has a proper gcd: the large global order excludes gcd N. If all checks are units, the B baby powers are distinct modulo every prime divisor of N. B=1 needs no checks. Global distinctness alone would be insufficient.

At any prime factor p, with `q=N/p`, we have `p=1 mod (p-1)` and `q=N mod (p-1)`. Consequently the true `S=s+m²t` satisfies

```
alpha^(u+vN-s) = beta^t mod p.
```

For each nonempty interval, use starts `t0=a_s+kB`, `0<=k<ceil(ell_s/B)`, and tagged giant

```
gamma_(u,v,s,t0) = alpha^(u+vN-s) * beta^(-t0) mod N.
```

All negative powers use a checked inverse. A baby match at j represents `S'=s+m²(t0+j)`. Record the actual final-block length, even if B babies are used for every block. A padded j may be rejected before recovery, or its candidate may be tested; neither branch loses a true match, by componentwise uniqueness.

For a global match, let `Delta=(S')²-4uvN`. If Delta is a nonnegative integer square, test both numbers

```
P = (S' +/- isqrt(Delta))/(2u)
```

for exact integral division, the relevant target interval if used, `1<P<N`, and `P|N`. Otherwise the tag yields no factor. This is a fixed-degree integer calculation with polynomial bit cost. Negative v, negative S', Delta=0, or a negative second root require no new assumption. The leading coefficient u is a positive integer, so `uP²-S'P+vN` is never the zero polynomial. Its reduction modulo some prime need not retain that degree; recovery is over the integers, not by inverting u modulo N.

If this is the true tag with true baby j*, global equality to baby j implies equality modulo p, so `j=j*`. The true p is an integer root, since `up²-(up+vq)p+vN=0`. Thus the true tag cannot be removed unsuccessfully. Check **every tag** associated with a global residue match before deduplicating or deleting that residue. There can be G matched tags, not merely B; distinct babies do not prohibit many giants sharing one baby.

After these checks remove globally matching giants. Form the monic product of remaining `(Y-gamma)` and evaluate it at all babies using fast polynomial arithmetic over `Z/NZ`. Such arithmetic does not invert arbitrary point differences. A proper product gcd is a factor. If a product gcd is N, one scan or product-tree descent finds a nonunit leaf. Every leaf difference is nonzero modulo N, so its gcd is proper. Only one successful localization is needed. Repeated prime factors pose no problem: several proper leaf valuations may combine to give product gcd N. The consumer requires a collision modulo a prime, not modulo its entire prime power.

**A6: full cost and all-composite reduction.** If K' is the number of nonempty root intervals, retain the exact giant count

```
G = sum_s ceil(ell_s/B) <= K' + T/B <= K + T/B.
```

Constructing the pairs, roots, integer endpoints and initial giant powers, retaining tags, sorting global matches, checking up to G quadratics, polynomial construction/evaluation, and the final localization are all included. Consecutive giants advance by the common `beta^(-B)`. Arithmetic has `O(log N)`-bit operands/exponents in the parameter regime here, with actual list-index and coefficient widths charged. In particular,

```
expected per-dyadic bit cost
  = (m+B+G) poly(log N)
  = O~(m + B + sqrt(N/m)/B).
```

The soft notation suppresses polynomial logarithms of N only. The `sqrt(B)` preparation is absorbed by B, and `T/B`'s additional `m/B` is absorbed by m. Choose the integer `B=max(1,ceil((N/m)^(1/4)))`. This is a mathematical composition using fast polynomial algorithms, not a benchmark of Python multiplication or a new installed solver.

For complete N-only coverage, the following is sufficient on the promised composite input:

1. Handle `N<=32` directly. Return 2 for even N. Test perfect powers by exact integer roots and return a proper base if found. The latter costs polynomial bit time, covers all prime powers, and leaves W018's at-least-two-distinct-primes promise satisfied. A square test alone would also suffice after the small-factor reduction below, but doing perfect powers first is convenient.
2. Put `h=max(5,ceil(N^(1/5)))`. Sieve through `2h` and take any prime `h<=m<2h` (existence follows from Bertrand's theorem). Then m is odd and `m<N`. Return `gcd(m,N)` if proper.
3. Let D be the least integer with `mD²>=16N`. Apply the small-factor product method through `min(D,floor(sqrt(N)))`. If a nonunit product occurs, localize to a proper integer factor. Its cost is `O~(sqrt(D))=O~(1+(N/m)^(1/4))`, including localization. A clipped leaf lies in `(1,N)`, which also handles prime powers safely. [Harvey, Proposition 2.5](https://arxiv.org/html/2010.05450#S2.SS3) supplies the square-root product machinery.
4. If the screen reaches `floor(sqrt(N))`, it must have succeeded on a composite. Otherwise enumerate `X=D,2D,4D,...` until X exceeds `floor(sqrt(N))`, using the parameters above and a truncated last interval. There are `O(log N)` intervals. Acquire the same alpha,beta once at the common B if desired and reuse them.

For these choices, `m<max(10,4N^(1/5))<16N^(1/3)`, hence `D>=4sqrt(N/m)>N^(1/3)`. An unfactored composite after the screen cannot have three prime factors counted with multiplicity: the smallest would be at most `N^(1/3)`. After excluding squares it is therefore a distinct semiprime. Every remaining least prime factor is in the enumerated intervals, which satisfy the explicit U,V guards. The identity/consumer proofs actually tolerate composite q, but that extra generality is not needed for this reduction.

Since `m=Theta(N^(1/5))`, the sieve, preprocessing, and logarithmically many dyadic searches all fit expected `N^(1/5) poly(log N)` bit work. Recursive splitting and primality testing would give complete factorization with additional polynomial logarithmic factors. The established review result is the splitter composition; no machine refinement, Lean proof, or full implementation was added. W018 makes this an **expected, always-correct** bound. A deterministic replacement of that primitive is a distinct obligation, not an inference from the deterministic comparators.

**A7: real root sharing, with the exact classes.** Write `chi(x)` for the Legendre symbol modulo m and choose a known nonresidue eta, lifted as a unit modulo m². For each `1<=u<=U`, choose `i in {0,1}` with `chi(u)=(-1)^i` and acquire one lifted root

```
A_u² = u * eta^(-i) mod m².
```

For every signed `v in {-V,...,-1,1,...,V}`, choose `j in {0,1}` with `chi(v)=(-1)^j` and acquire

```
B_v² = v * eta^(-j) mod m².
```

Classification is on v itself: `chi(-v)=chi(-1)chi(v)`. Copying the positive-v class/root to negative v is generally wrong. These are unit radicands, so their simple roots lift by the formula already given.

Let `chi(N)=(-1)^k`. Exactly those classes with `k+i+j` even admit roots of `4uvN`. For each admissible h=i+j, take `C_h²=N eta^h mod m²`. Then

```
(2 C_(i+j) A_u B_v)² = 4uvN mod m².
```

The plus and minus of this unit are the two roots, independently of the initially chosen signs for A, B and C. Only **one** extra square-root acquisition is needed for C: if k=0, acquire C0 and set `C2=eta*C0 mod m²`; if k=1, acquire C1 for the two off-diagonal classes. Treating h=2 as h=0 without its eta multiplier would be an error.

Thus at most `U+2V+1` square-root calls, their Legendre tests and lifts, plus nonresidue acquisition, produce an implicit root representation. The saving from O(UV) root calls to O(U+V) is valid. It does not remove O(UV) multiplications/reductions if the pair roots are subsequently materialized; the original explicit loop still examines Theta(m) pairs. For example, if `m=3 mod 4`, exactly one of +v and −v is admissible for each positive u,v, so there are exactly `2UV` root records before interval clipping. A uniform claim that the root records have disappeared would already be false in that case.

**Carries cannot be discarded.** For each choice of sign and class, use integer representatives and put

```
r = +/- 2 C_(i+j) A_u B_v,
c = floor(r/m²),
s = r-m²c in [0,m²).
```

The exact identities are

```
alpha^s = alpha^r * beta^(-c),
gamma = alpha^(u+vN-r) * beta^(c-t0),
S = r + m²(t-c).
```

They hold for negative r using mathematical floor. The admissible interval for `t-c` is shifted by this pair's own carry; its width is unchanged only if the shift is retained. For baby j, the corresponding cleared difference is

```
alpha^u * (alpha^N)^v - alpha^r * beta^(t0+j-c).
```

This specifies the “appropriate corrections” in the parent row expression. Keeping r directly as an unreduced exponent is legal, with its actual bit length; it does not make the shifted endpoints or tag disappear. Canonical A,B,C representatives give `|r|<2m^6` and `|c|<=2m^4+1`, still logarithmic-width integers here. The problem is paying for pair-dependent work, not claiming that one such binary exponentiation has cost proportional to the numerical exponent.

In a formal row polynomial, B_v may be as large as `m²-1`. Dense expansion must pay its actual degree, and multiplication over many v can add those degrees. A sparse display with V factors is not a fast product/evaluation algorithm. Nor may exponent identities modulo m² be used as identities of powers modulo N: that would require `alpha^(m²)=1`, contrary to the acquired beta order. These are accounting constraints on the proposed implementation, not a general lower bound on possible implicit algorithms.

**The unbalanced acquisition boundary matters.** The completed parameters have

```
U+V = O(1 + sqrt(mN)/X + sqrt(m)*X/sqrt(N)).
```

At `X=Theta(sqrt(N))`, this is O(sqrt(m)). Near the legal lower endpoint `X=Theta(sqrt(N/m))`, however, U is Theta(m) and V is Theta(1). Thus A7 does not by itself reduce even the coordinate-root acquisition to O(sqrt(m)) throughout the all-input dyadic schedule. With the proposed `m=Theta(N^(1/3))`, that endpoint can cost Theta(N^(1/3)), while the formal target is N^(1/6). A claim confined to balanced semiprimes would avoid this particular endpoint, but is a different scope.

**Primary-art comparison: known mechanisms, no priority inference.** All comparisons below use the bodies and algorithm proofs in the frozen HTML/MathML, not abstract metadata. The [source manifest](W019-public-cover-review-evidence/primary-sources/manifest.json) records URL, acquisition time, byte hashes and reading-aid hashes. This is a bounded comparison against the three requested papers, not an exhaustive literature survey.

Harvey 2010.05450, §3 and Algorithm 4.2/Proposition 4.2, already searches weighted sums, transfers them to modular powers, shares a baby table across tagged coefficient pairs, checks component orders, recovers full matches quadratically and removes them before product gcds. Its envelope is `O~(r+B+sqrt(N/r)/B)`, matching A6 after renaming r to the present m. Its coverage uses real approximation and positive `ab<=r`, unlike the signed modular rectangle here. Theorem 1.1 proves deterministic `O(N^(1/5) log^(16/5)N)`. Remark 3.4 already discusses a prospective N^(1/6) from fully sharing the larger search. A6 therefore supplies no new exponent or new shared-consumer principle. [Primary algorithm and proof](https://arxiv.org/html/2010.05450#S4).

Harvey–Hittmeir 2105.11105, Proposition 3.3 equations (3.4)/(3.6), uses `-aN/sigma+b sigma=0 mod m` to make `aq+bp=aN/sigma+b sigma mod m²` for `p=sigma mod m`. Under `a=v,b=u,sigma=p mod m`, its condition is precisely W019's covered stationary relation. With `F(x)=ux+vN/x`, independently expanding `F(x)^2-4uvN=(ux-vN/x)^2` shows why its residue is a square root of the same discriminant expression. W019 enumerates short coefficients then roots; this paper enumerates factor residues and constructs lattice coefficients. They are different enumerations of an essentially known modular weighted-sum constraint. Algorithm 4.3 already uses an m²-powered stride and global-match removal. Its main theorem adds a log-log saving at exponent 1/5. These passages do not provide A7's bilinear root evaluator. [Primary proposition and main search](https://arxiv.org/html/2105.11105#S3).

Gao–Feng–Hu–Pan 2512.19076, Algorithm 4.3/Lemma 4.4/Proposition 4.5, constructs nonzero quadratics from second vectors in rank-3 lattices, then uses m²-powered babies, tagged quadratic recovery and the established collision consumer. Algorithm 4.6 separately prices factor-or-powered-component-order preparation when m's factorization is known. Proposition 4.9/Corollary 4.10 give the paper's balanced-semiprime logarithmic refinement at exponent 1/5; §5 uses supplied residue information. None of these passages supplies A7's root sharing or a sublinear evaluator for its signed pair family. I do not certify this entire paper's bounds: for example, Proposition 4.5 bounds the absolute value of its integer quotient but searches nonnegative babies without a displayed sign branch; its match-count discussion also needs tagged multiplicities. Signed ranges and counting matches by giant tags are explicit here. These local observations do not establish that the paper's asymptotic claim is false. [Primary main search and proofs](https://arxiv.org/html/2512.19076#S4).

A7 itself is elementary multiplicativity of square classes plus unique lifting. The checked algorithm sections do not state its exact array formula; the full-source keyword search is also preserved in the read scope. That absence is not a priority result. **Treat the modular weighted-sum idea and shared BSGS consumer as established machinery, and A7 as a correct elementary representation with no demonstrated new factoring computation.**

**Precise remaining computation.** A claim below the explicit m budget needs a concrete procedure on the public coordinate data, alpha,beta, and exact integer bounds, that does all of the following within its claimed budget:

1. Represents the admissible character-class/sign pairs and their pair-dependent carries, intervals and block starts without enumerating them at Theta(UV) cost, while preserving the covered pair.
2. Evaluates the required collision products at the B babies, or supplies another fully specified collision test, without expanding all pair records or a hidden dense degree. The output may be a factor rather than a full list; there is no requirement to output every collision merely because the explicit algorithm does.
3. Handles full-modulus equality with tag-sensitive integer recovery or an equally safe implicit substitute. Enumerating all unsuccessful global tags, deleting an unexamined true tag, or receiving a full product gcd without paid localization would invalidate the claimed saving.
4. Pays for prime/nonresidue selection, all coordinate roots and all dyadic ranges, including the unbalanced endpoint. The current O(m) sieve and Theta(m) coordinate acquisition in that endpoint must actually be replaced or avoided. No lower bound on other prime-acquisition methods is asserted.

If **all** of this had cost `O~(sqrt(m)+B+sqrt(N/m)/B)`, with the paid small-factor preprocessing, then choosing `B~(N/m)^(1/4)` and `m~N^(1/3)` would give the formal N^(1/6) target. This is a conditional algebraic balance only. A7 does not meet it. Root sharing alone changes neither the existing ceiling-sensitive G nor the explicit pair traffic. W008's random additive-sum detector audit provides no impossibility proof for these known-prime multiplicative roots.

**Disposition and evidence limits.** Accept the cover, simple-root construction, signed transfer, integer recovery, tagged collision consumer, and root-sharing algebra. Complete their specification with the constants, empty/negative-index handling, class factors and carry signs above. Accept an all-composite expected one-fifth mathematical upper bound using imported primitives. Reject treating that bound as a deterministic improvement, deleting m/ceilings/acquisition/degree costs, or treating the N^(1/6) target as achieved. The next meaningful object is the explicit implicit-collision procedure with the four obligations above, not another unpriced notation for the product.

No numerical certificate, parameter sweep or factoring experiment was run: universal identities and integer inequalities decide this audit, and the unresolved algorithm is absent rather than falsifiable by a performance run. [Method and run status](W019-public-cover-review-evidence/method-and-run-status.json) records zero runs and retained read-output truncations. No installs, recursive delegation, commits, shared solver/Lean/STATE/registry/task-file edits, or solver/Lean validation claims occurred. Only this report and its assigned evidence directory were written. Frozen-input integrity and live drift are recorded separately; any subsequent parent construction is outside this frozen A1–A7 verdict.

At delivery, all frozen input hashes matched. Only STATE had changed among those live inputs; its preserved diff was read for context. It records the parent's separate root/carry continuation, which is not an additional reviewed authority here. The W019 snapshot and all mathematical input reports were unchanged. The [delivery manifest](W019-public-cover-review-evidence/delivery-manifest.json) inventories the report and evidence; [delivery.sha256](W019-public-cover-review-evidence/delivery.sha256) also hashes that manifest, excluding itself to avoid self-reference.
