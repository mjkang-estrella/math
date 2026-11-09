# W008 — independent review of the affine random grid note

2026-10-08. T3 review child (Claude Opus 5.5, user-authorized). Symbolic proof
and source reading only. No candidate execution, parameter sweep, solver,
registry, STATE, or Lean change. Verified COMPLETE factoring improvement: **NONE**.

Scope: [W008-random-affine-grid.md](W008-random-affine-grid.md) only. This review
does not duplicate W008 A (arbitrary four lists, composed-sum detector) or W007 D
(residual dynamics). No unreviewed scope from the four-list brief is imported.
I use only these elementary facts from it: the second-moment inequality,
the one-path full-gcd descent, and the 131-prime threshold arithmetic. Each is
re-derived below for the grid generator.

## Verdict

| Claim in the note | Status |
|---|---|
| Pairwise-independent useful law for K<=p | **CONFIRMED** |
| Global-zero union bound K^4/N | **CONFIRMED**. It needs only uniform marginals, so it holds for every K. |
| Threshold success >1/3 for p,q>=131 | **CONFIRMED** (>=0.378) |
| N-only schedule | **REPAIRED**. The note's monotonicity step is false in the K>p range, but a separate covering argument (§1.3) closes that range. The expected cost is O(sqrt(p)·poly(log N)). |
| Exact composite-ring block product, (m^4+h^4)·poly cost | **CONFIRMED**. The constant improves with per-coordinate splits. Descendant boxes cost O(sqrt\|B\|), so recovery adds no log K factor. |
| "m^4+h^4>=2K^2 within the single-block scheme" | **CONFIRMED** (AM–GM). This is a statement about that scheme only. |
| Generic X-shift overlap I(h) and quotient degree K^4−I(h)>=K^3 | **CONFIRMED** over Q(a_1..a_4). Specialization needs the corrections in §3.3. |
| Bostan–Yurkevich or another holonomic N-th-term theorem beats K^2 here | **NO**. See §4. |
| Sub-K^2 program | **None found.** Only the precise recurrence classes in §5 are closed. |

Strongest scoped result: for distinct odd primes 131<=p<q, with N the only input,
there is an expected O(sqrt(p)·(log N)·polylog(N)) bit-operation Las Vegas splitter
from five random residues per trial. It uses the exact monic block product over
Z/NZ and one-path full-gcd recovery. This is a **genuine control** at the known
p^(1/2) collision scale, not an improvement.

## 0. Read scope and hashes

Required reads (SHA-256, unmodified):

    dc826260f9df986dd899270772d05443d6e3a3b6db521921969ccf1c370cc094  AGENTS.md
    b460bb1785ef5f2514a475054962d515f2210a855b474497a5291e524bf53185  RESEARCH_TEAM.md
    a1491eabfb67a9df1eb76ed5eb689c5165173ae995c859baa3d8b5f3436a46e1  RESEARCH_LOOP.md
    b91bb2101c18e59706959612683e9b8c18b7bbdafe02bddfce7abbf705c3344f  README.md
    257511f8150bdeea977c38e3a83c6751d000fb7070eb13d12d50e0c94d008fb7  docs/SPECIFICATION.md
    a913082a9fe1f837cd91c92e52f9cd132450e2e3e3df6f02e58c525aa3232ea9  research/findings/W008-random-affine-grid.md
    15f975e86948f62238e5066028dc99cc6084e2ba37591f7dfda37c211dece766  research/findings/H030-disposition.md
    7051c5621811ac85172c6e680991ef17900126ce082e60beab562a65b03a9e22  research/findings/H030-root-product-blocks.md

The last two H030 files were consulted for conventions only, in particular the
monic product/remainder paragraphs of H030-root-product-blocks.md.
The text of W008-random-affine-grid.md agrees with the affine note in the brief.
The W008 A report exists, but I did not read it, to keep this review independent.

Primary source, fetched into
[W008-affine-grid-review-sources/](W008-affine-grid-review-sources/):

    f3d617af2e9c899b41d5f4d9120412c78857ebc19009b69fe99e74d97f0d9b09  BY-2012.08656.pdf  (arXiv v1, 15 Dec 2020, 33 pp.)
    f3d50b7cc29175918aff4cab5c5b1a0c36f2c601b041b42061430a8d45ef2717  BY-2012.08656.txt  (pdftotext -layout)
    38f11104eef5dbc964778dddbb59d080c40ed00acf3358b235c6efa6e077c33f  BY-2012.08656v1.abs.html

Sections read: the abstract and introduction (pp. 1–3); §2.1–2.2 (Algorithms 1–4);
§3.1–3.5, which contain Definition 1, Theorems 1, 3, 5, 6 and 8 and Corollaries 2, 4 and 7;
the curvature discussion on p. 22; and §6, the future-work list.

The only numerical work was exact arithmetic on the threshold constants listed in
§1.2 (for example 0.49817, 0.11946 and 4·(2/3)^4). These check certificates; they
are not candidate runs.

## 1. Generator, success law and schedule

### 1.1 Pairwise law (K<=p) — confirmed

Take (b,a_1..a_4) uniform modulo N. By CRT, their reductions modulo p and modulo q
are independent and uniform. For v≠w in [0,K)^4 with K<=p, every coordinate lies in
[0,p−1], so v≢w (mod p), and hence also mod q. Therefore (1,v) and (1,w) are linearly
independent over F_p and over F_q. The map (b,a)↦(L_v,L_w) has rank 2, so the pair
is uniform on F_p^2 and on F_q^2. Write I_v=[p|L_v]·[q∤L_v]. Then

    P(I_v=I_w=1) = p^-2 (1−1/q)^2 = a^2,  a=(1/p)(1−1/q),

so the indicators are pairwise independent Bernoulli(a) variables. With Z=Σ I_v
and λ=K^4 a, we get E Z^2=λ^2+λ(1−a). Cauchy–Schwarz gives
Pr[Z>0] >= λ/(λ+1−a), exactly as stated.

The roles of b also check. Without b, v=0 gives L_0=0 identically, and
L_{2v}=2L_v makes events dependent. The offset b removes both problems.

### 1.2 Global zeros and the threshold — confirmed

Each L_v is uniform mod N because b is uniform. This holds for every K, including
K>p. So Pr[∃v: N|L_v] <= K^4/N.

Let K* be the first power of two with K*^4>=p. Then K*^4<16p, so K*<2p^(1/4)<=p
for p>=3. At this stage λ>=1−1/q. The function λ/(λ+1−a) increases in λ, and its
worst case as p→∞ with q>=137 is 0.49817>0.49. Also K^4/N<16/q<=0.1168.
**Success >= 0.381 at K*.**

### 1.3 N-only schedule — correction and repair

The note doubles K up to K_cap, the first power of two with K^4>=ceil(sqrt N),
and then repeats K_cap. For unbalanced N, for example p≈2^20 and q≈2^1000,
K_cap≈N^(1/8)≫p. The pairwise law is therefore **unavailable** on all stages with
K>p, so the note's claim "λ is at least the threshold value, same lower bound" is
unsupported there. (Pairwise independence actually fails: v≡w mod p gives
L_v≡L_w mod p.)

**Repair (fresh proof for K>=p).** If a_1 is a unit mod p (probability 1−1/p),
then for each fixed (v_2,v_3,v_4), letting v_1 run over [0,p)⊂[0,K) hits
L_v≡0 (mod p) exactly once. So a p-zero exists with probability >=1−1/p>=0.992.
A p-zero together with no global zero is all that recovery needs (§1.4).

For every stage K*<=K<=K_cap:

    K^4/N < 16·ceil(sqrt N)/N <= 0.11947    (worst case N=131·137),
    success >= min(0.4981, 0.992) − 0.1195 >= 0.378 > 1/3.

Stages with K<=p use §1.1, where λ is monotone in K. Stages with K>=p use the
covering argument. K*<=K_cap holds because p<sqrt N.

**Paid schedule.** First remove primes up to 127 by trial division. Then, for
K=1,2,4,…,K_cap, run t=4 independent trials per stage, and repeat K_cap
indefinitely. Each trial has expected cost C·K^2·polylog (§2). Since
4·(2/3)^4=0.790<1, the expected work past K* forms a convergent geometric series:

    E[work] = O(K*^2 · polylog) = O(sqrt(p) · (log N) · polylog(N)),

using K*^2<4 sqrt(p). With t=3 the series is not certified: 4·0.63^3 is about 1.0002.

This is Las Vegas. Outputs are verified divisors, and there is no worst-case time
bound. p is never used. No dovetail with external evaluators is needed.

### 1.4 Proper-gcd localization — confirmed, with an exact invariant

Invariant: the current box B (a product of four integer intervals) has
gcd(R_B,N)=N. Split one non-singleton side into B_1⊔B_2, so R_B=R_{B1}R_{B2}.

* If g=gcd(R_{B1},N) is proper, return it.
* If g=N, descend into B_1.
* If g=1, then R_{B1} is a unit, so gcd(R_{B2},N)=N. Descend into B_2 without
  evaluating it.

A singleton box with gcd N is a global zero. So on the event {∃ p-zero} ∩
{no global zero}, the root gcd lies in {p,N}, and the walk returns a proper factor
before any leaf. It makes at most 1+Σ⌈log2 K_i⌉ <= 1+4⌈log2 K⌉ box evaluations.
Translation step: a subbox Π[l_i,l_i+K_i) has L=(b+a·l)+a·u with u∈Π[0,K_i), so the
compact representation (b',a,K_1..K_4) costs O(1) mod-N operations to update.

## 2. Exact monic block product over Z/NZ and its full cost

### 2.1 Construction for any box Π[0,K_i), without padding or extra leaves

Per coordinate, choose m_i=⌈sqrt K_i⌉, h_i=⌊K_i/m_i⌋ and r_i=K_i−m_i h_i<m_i. Split
[0,K_i)=A_i⊔B_i with A_i=[0,m_i h_i) and B_i=[m_i h_i,K_i). The box splits into at most
16 pieces indexed by S⊆{1..4}, using A_i for i∈S and B_i otherwise; empty pieces
are skipped. For piece S:

    F_S(T) = Π_{r ∈ Π_{i∈S}[0,m_i) × Π_{i∉S}B_i} (T + Σ_i a_i r_i)   (monic, degree D_S)
    points x_q = b + Σ_{i∈S} m_i a_i q_i,  q ∈ Π_{i∈S}[0,h_i)       (P_S points)
    R_piece = Π_q F_S(x_q),     R_B = Π_S R_piece.

This is exact because every u∈B has a unique decomposition u_i=r_i+m_i q_i on A_i
coordinates, and u_i itself on B_i coordinates. Bounds:
D_S <= Π m_i <= Π(sqrt K_i+1) <= 16 sqrt|B|, and P_S <= Π h_i <= sqrt|B|.

**Dyadic refinement.** In the power-of-two schedule with halving descent, every
box has sides 2^(k_i). Choose α_i<=k_i with Σα_i=⌊Σk_i/2⌋ and use m_i=2^(α_i),
h_i=2^(k_i−α_i). Then there is one piece with D+P <= 2^⌊S/2⌋+2^⌈S/2⌉ <= 2.13 sqrt|B|.

Correction to the note: its single m=2^⌊log2K/2⌋ gives m^4+h^4=4.25K^2 when
log2K is odd. Per-coordinate exponents give exactly 2K^2, which matches the AM–GM
floor Π m_i·Π h_i=|B| ⇒ D+P>=2 sqrt|B| for this scheme.

### 2.2 Operations (all ring-generic over Z/NZ)

1. **Setup.** Compute the shifts Σa_i r_i and the points x_q by incremental
   addition (plus four products m_i a_i). Cost O((D+P) log N) bits.
2. **Product tree of monic linear factors.** All products are monic; no inverses.
3. **Multipoint evaluation by a monic remainder tree.** If P>D, split the points
   into ⌈P/D⌉ groups. If P<D, first reduce F_S modulo the monic root subproduct.
   Division by a monic polynomial uses Newton inversion of the reversed polynomial,
   which has constant term 1, so no division by ring elements occurs and no
   non-unit pivots or gcd side branches arise.
4. **Products.** Multiply the P values mod N, multiply the pieces, then take one
   gcd with N.
5. **Polynomial multiplication.** Degree-D multiplication over Z/N uses Kronecker
   packing with slots of 2⌈log2N⌉+⌈log2D⌉+1 bits, then one integer product
   M_Z(O(D(log N+log D))), then coefficient reduction mod N.

Bit cost per box: O(M_Z((D+P)(log N+log K))·log(D+P)) = Õ(sqrt|B|·log N). Scratch
is O((D+P)(log N+log K)·log(D+P)) bits if whole trees are kept, and less if they
are streamed. No factorial denominators appear, no field interpolation, and no
invertibility conditions beyond monicity, which holds identically.

**Recovery is geometric.** In the dyadic case, the j-th descent box has size
K^4/2^j, so the walk costs Σ_j 2.13·K^2·2^(−j/2) <= 7.3·K^2 records, plus the
root's 2K^2. The total per trial is O(K^2·(log N)·polylog(K log N)), with no extra
log K factor. The general 16-piece version gives the same O(sqrt|B|) per box.

Conclusion: the composite-ring K^2 control holds as claimed, including setup,
point records, output products, bit multiplication and recovery.

## 3. Shift quotient degree

### 3.1 Symbolic slopes — confirmed

G_K(X)=Π_v(X+a·v) over Q(a). The forms a·v are pairwise distinct for distinct
integer vectors, so G_K is squarefree. G_K(X+γ) and G_K(X) share the root −a·v'
iff γ=a·(v'−v) with v,v'∈box. For γ=a·h this forces v'=v+h, and the count is

    I(h) = #{v : v, v+h ∈ [0,K)^4} = Π_i max(0, K−|h_i|).

The gcd has degree I(h). The reduced numerator and denominator of
G_K(X+γ)/G_K(X) each have degree K^4−I(h). Over h≠0, max I(h)=K^3(K−1), attained
only at h=±e_i, so the minimal reduced degree is exactly K^3. For γ outside
{a·h : |h_i|<K} the gcd is 1. **Confirmed as stated.**

### 3.2 The note's X-shift is the wrong index for N-th-term algorithms; the right index gives the same K^3

The algorithms of Chudnovsky, BGS and Bostan–Yurkevich (BY) need a recurrence in a
sequence index n, not a shift in the evaluation variable. The natural candidate
slices one coordinate:

    u_n = Π_{v: v_1<n} L_v,   u_{n+1} = g(n) u_n,
    g(t) = Π_{w∈[0,K)^3} (b + a_1 t + a'·w),   deg_t g = K^3 (leading coeff a_1^(K^3)).

This is an exact first-order hypergeometric recurrence of length N=K and degree
d=K^3. The baby-step/giant-step cost √(N·d)·polylog equals √(K^4)=K^2, so it
reproduces the block algorithm and gives no saving.

**Lemma (all orders, for this sequence).** Suppose Σ_{i=0}^r c_i(n) u_{n+i}=0 holds as
a polynomial identity in n over Q(a,b), with u_n=Π_{j<n} g(j). Then some c_i has
deg >= deg g.

Proof: let i_0 be minimal with c_{i0}≠0. Divide the identity by Π_{j=n}^{n+i0−1} g(j).
Every remaining term with i>i_0 is divisible by g(n+i_0), so g(n+i_0) | c_{i0}(n).

Since Theorem 5-type costs grow with √(N·d), higher order does not help this
sequence.

**Scope caveat (discovery cost).** If the recurrence is required only for
0<=n<N, as for an actual N-th-term computation, low-degree recurrences always
exist by interpolation. For example, take the degree-(K−1) interpolant ĝ of
g(0..K−1). But writing ĝ requires the K values g(j), which is the original
problem. A recurrence counts only when its coefficients are derived from the
generator at a paid cost. The lemma closes recurrences that are symbolic
identities in (a,b,n). It does not close every finite-range recurrence whose
coefficients come from a cheaper source.

### 3.3 Specialization — corrections

For numerical slopes in a field, deg gcd(G(X+γ),G(X))=Σ_ρ min(mult_ρ G(X+γ), mult_ρ G(X))
>= the generic I(h). Specialization can only increase cancellation, so the generic
degree K^4−I(h) is an **upper bound** on the specialized reduced degree, not an
equality.

* **Exact sufficient condition** (integer or field slopes) for the count to equal
  I(h) and G to be squarefree: a·u≠0 for every nonzero integer u with
  |u_i| <= 2(K−1)+|h_i|. For |h_i|<K this means |u_i|<=3K−3, which holds, for
  example, for integer slopes a_i=B^(i−1) with B>6K−6. (Condition: v'−v−h must be
  separated.)
* **Aligned slopes** a_i=aK^(i−1): G is squarefree, but γ=a gives overlap K^4−1.
  The quotient has degree 1, a length-K^4 arithmetic progression whose
  factorial-type evaluator costs √(K^4)=K^2 (confirmed). Also note that aligned
  slopes are the AP product Π_{j<M}(b+aj) with M=K^4. An evaluator below K^2 that
  is **uniform over all slopes** would therefore give AP products mod N below
  √(length). That is the open fast-factorial-mod-N problem, which underlies
  Pollard–Strassen and Harvey-type deterministic bounds. Under random slopes,
  aligned grids occur with probability about 0, and I know no random-to-worst
  self-reduction (R has degree K^4 in a, far beyond interpolation range). So
  the open problem does not constrain the random promise, and nothing transfers
  in either direction.
* **The operating modulus is never generic.** Modulo p in the operating range
  K^4>p (strict for K a power of two and p odd), pigeonhole gives v≠w with
  a·v≡a·w (mod p). G mod p is **not squarefree**, and shift overlaps exceed I(h).
  These coincidences depend on the hidden p. A uniform algorithm over Z/N cannot
  select them without information equivalent to the factor. The symbolic count
  therefore constrains only identities valid in Z[a,b] (equivalently, generic
  slopes). It does not cover p-specific identities. Examples of the latter are
  Π_{j∈F_p}(x−j)=x^p−x, or x^D−y^D for a known element of exact order D. Each needs
  hidden group-structure information.

No all-order recurrence or factoring lower bound is claimed.

## 4. Bostan–Yurkevich (arXiv 2012.08656v1) — exact scope

* **Object.** A q-holonomic sequence (Def. 1) is c_r(q,q^n)u_{n+r}+…+c_0(q,q^n)u_n=0,
  with one index n, over a **field** K, with q∈K\{1}.
* **Arithmetic cost.** Thm 3: the sequence term u_N costs O(M(√N)) when
  c_r(q,q^k)≠0. Thm 5: O(r^θ√(Nd)+r^2 M(√(Nd))), where d=max deg_y c_j. Thm 1 covers the
  q-factorial and the Pochhammer symbol (α;q)_N.
* **Bit cost.** Thm 8 applies when K=Q, using binary splitting. Its cost is Õ(N^2 B)
  bits, for an exact rational output of size Θ(N^2 B). It is not a modular evaluator.
* **Algorithm 3.** Step 1 is division-free. Steps 2–3 (chirp evaluation) invert Q.
  Over Z/N a non-unit Q would only expose a gcd. The roots-of-unity remark (p. 14)
  shows that collapses need an element of known small order.

**Applicability to the grid.**

1. Grid leaves are additive, b+a·v, not polynomials in q^n. BY covers q≠1. The
   additive analogue is the q=1 case of Chudnovsky/BGS (BGS 2007 is already in the
   repo as H030-block). For the slicing sequence, those methods give √(K·K^3)=K^2.
   The lexicographic full-index sequence has ratio b+a·digits(n). That is not a
   bounded-degree polynomial identity in n unless the slopes are aligned, and then
   d=1 and N=K^4, giving K^2 again.
2. A multiplicative grid variant would make BY apply literally. Examples are
   leaves α−Πg_i^(v_i), or g_i=g^(K^(i−1)), which form a single geometric progression of
   length K^4. But Thm 1/5 cost √(N·d) is still √(#leaves)=K^2. That variant would also
   need a new success law, because L_v−L_w is no longer independent of b.
3. BY treats multivariate q-holonomy only as background for creative telescoping
   (p. 3). It gives no multi-index N-th-term algorithm.

**Answer: no.** No BY theorem, and no q=1 analogue I checked, beats the K^2
evaluator. Once recurrence degree, order, discovery and initial values are paid,
every applicable instance has √(N·d)>=√(K^4). A Barnes multiple-gamma expression
for Π(b+a·v) is a name, not a modular evaluator, and it is not used.

## 5. Sub-K^2 program?

None emerges. This review closes the following:

* **(C1)** Single-block and 16-piece materialized splits, which need >=2 sqrt|B|
  records.
* **(C2)** Hypergeometric coordinate-slicing recurrences of any order, when valid as
  symbolic identities. The lemma in §3.2 forces degree >=K^3 and cost >=K^2.
* **(C3)** Literal application of BY/BGS/Chudnovsky N-th-term theorems, additive or
  multiplicative.
* **(C4)** p-specific collapses (x^p−x, roots of unity of known order), which need
  hidden-factor information.

**Not closed, and named as the changed computation.** The open route is a
representation R=Π_{n<N} c(n) whose coefficient c has low degree in n but **high
degree in b**. Each value c(n) would itself be a complete product over a disjoint
grid sub-block, as in a pencil (1−n)P_0+nP_1 or a low-degree curve of totally
split polynomials, and the c(n) would be evaluable more cheaply than their size.
Such a family would allow recursion T(M)=O(1)·T(M/N)+√N. In characteristic 0 and
over Z/N without a factor, no finite additive subgroup exists, so translates of
a block cannot be the fibres of a polynomial map. Any such family needs
**non-translation** fibre structure.

Related prior art (abstract only, unverified body): Lipton,
*Straight-line complexity and integer factorization*, ANTS-I 1994, LNCS 877,
71–79, doi:10.1007/3-540-58691-1_45. It shows that short straight-line programs
for polynomials with many rational roots would make factoring easy.

A grid evaluator that is an SLP in b with integer slopes would be such a program
for a polynomial with K^4 distinct integer roots. So this route sits inside a
known hard question (cf. the Shub–Smale τ-conjecture). I make no claim about its
truth.

## 6. Next constructive gate

Do not proceed with a structured-split family unless it meets all of these:

* It gives an explicit family {c(n)} with deg_n c=d, together with grid sub-blocks
  S_n that are disjoint, cover the box, and are generated from (b,a) alone.
* It proves c(n)=κ_n Π_{v∈S_n}(b+a·v) as a symbolic identity, with κ_n units mod N.
* Its coefficients are computed in o(K^2) total, discovery included.
* It keeps the §1 success law and the §1.4 descent. Subboxes must stay in the family,
  or else the recovery must be re-proved.

The cheapest falsifier is a symbolic check at K=2 or K=4 over Q(a,b): either such
a family exists with N·d<K^4, or the pencil/curve constraint (P_1−c_n P_0 vanishing
on S_n is overdetermined for N>=3) rules it out for that block shape. No numerical
run is needed or authorized.

Verified improvement: **NONE**. Disposition: the affine-grid generator, its schedule
(repaired) and the K^2 composite-ring evaluator are **ACCEPTED as a control**. The
recurrence shortcut is **CLOSED** within the scope of §5 (C1–C4).
