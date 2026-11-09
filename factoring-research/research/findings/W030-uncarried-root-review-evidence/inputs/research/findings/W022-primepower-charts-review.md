# W022 review: valuation strata and prime-power root charts

2026-10-08 local / 2026-10-09 UTC. **Accept A, A2, and A3 as a repaired covering representation with polynomial integer exponents. Accept the displayed balanced exponents and reject the proposed generic dense evaluation composition as a speedup. Verified new complete factoring improvement: NONE.** The important completions are exact stratum bounds, signed chart endpoints, explicit construction and localization interfaces, and the distinction between balanced carry bounds and a complete factor-range schedule. This is not a factoring lower bound.

The audited W022 snapshot has SHA-256 `46af485d802c5303f8eb920d7691519c74a9fbc68beea41eeae49cd0567a2d67`. The [verbatim brief](W022-primepower-charts-review-evidence/task-brief.md), [frozen inputs and hashes](W022-primepower-charts-review-evidence/input-manifest.json), and [method/read scope](W022-primepower-charts-review-evidence/method-and-read-scope.json) fix the boundary. W022 §B is excluded. W019, W020, and W021 are imported only at their accepted interfaces; their certificates and underlying implementations were not re-audited. The parent remains the constructive researcher. No numerical certificate was needed or executed.

## 1. Composite-modulus cover and exact primitive strata

Let ℓ be a **fixed odd prime**, k≥1, M=ℓ^k, gcd(N,ℓ)=1, and N=pq with p prime and q a positive integer. The covering algebra does not require q prime. Require integer `1≤U<M`, `V=ceil(M/U)<M`; in particular U≥2, V≥2, and `M≤UV<M+U<2M`. The case U=1 is outside this contract, not a missing stratum.

Put z=p/q modulo M. Both p and q are units modulo M. The U+1 residues jz for 0≤j≤U are distinct even though M is composite: a congruence between two would imply M divides a nonzero index difference of magnitude <M. Sort their representatives in [0,M−1]. One consecutive positive gap d is at most floor((M−1)/U)≤V. If h is the corresponding signed difference of original indices, then hz=d modulo M and 0<|h|≤U. Taking u=|h| and v=sign(h)d gives

```
1≤u≤U,  1≤|v|≤V,  up−vq≡0 (mod M).
```

This is an existence proof using hidden p/q, not an instruction to compute it. The public algorithm constructs all strata/charts from N and the range parameters. Negative v is essential; for z=−1 the witness u=1,v=−1 is immediate.

For every covered pair define νℓ(v)=νℓ(|v|). Since both nonzero weights have magnitude <M, their valuations are <k. They are equal: if νℓ(u)=s<νℓ(v), dividing up−vq by ℓ^s leaves a unit minus an ℓ-multiple, contradicting divisibility by ℓ^(k−s). The symmetric case is identical. Thus let r=ℓ^s and divide **both** weights by r, exactly over the integers, including a negative v. Then

```
0≤s≤smax=floor(log_ℓ(min(U,V)))≤k−1,
m_s=M/r=ℓ^(k−s),    Q_s=m_s²,
U_s=floor(U/r),     V_s=floor(V/r),
1≤u'≤U_s,          1≤|v'|≤V_s,
ℓ∤u'v',            u'p−v'q≡0 (mod m_s).
```

Every index in 0..smax has a nonempty *public pair domain* (it contains (1,±1)); larger indices have an empty coordinate. In particular h=k−s≥1: there is no modulus-1/root-degeneracy branch. The word “primitive” means ℓ-primitive, not necessarily gcd(u',v')=1. Conversely, every primitive pair in stratum s lifts to (ru',rv') in the original rectangle; if its congruence holds modulo m_s, the lifted congruence holds modulo M. This is an exact decomposition of covered pairs, not merely one-way witness preservation. The same numerical primitive pair appearing at different strata corresponds to different lifted weights and must retain its occurrence.

For an integer public bound W≥0 with |up+vq|≤W for the original witness, set W_s=ceil(W/r). Division yields |S|≤W_s for S=u'p+v'q, and

```
S²−4Nu'v'=(u'p−v'q)²≡0 (mod Q_s).
```

The radicand is a unit. Over an odd prime power it has either zero roots or exactly two simple roots; no unstripped nonsimple-root formula is used. The ceiling in W_s is conservative. An integer floor would also preserve this particular inequality, but keeping the specified ceiling is safe and its rounding cost is included below.

An explicit odd-prime obstruction explains why s>0 cannot be omitted. Take M=81, U=V=9, z=28=1+27. For positive unit u in {1,2,4,5,7,8}, the least-magnitude signed residues zu modulo 81 are respectively 28,−25,31,−22,34,−19, all outside [−9,9]. There is no unit-weight witness. Yet (u,v)=(3,3) works and divides to (1,1) modulo 27. Replacing z by −28 gives the same unit obstruction and witness (3,−3). These are symbolic residue examples, not experiments or supplied factors to a solver.

The exact number of signed primitive pairs in stratum s is

```
P_s=2(U_s−floor(U_s/ℓ))(V_s−floor(V_s/ℓ)) ≤2UV/r².
```

For each canonical root a∈[0,Q_s), the exact retained lift interval is

```
ceil((−W_s−a)/Q_s) ≤ τ ≤ floor((W_s−a)/Q_s).
```

Its length is zero if the endpoints cross and otherwise at most 1+2W_s/Q_s. Thus canonical-root occurrences, with repetitions counted, are bounded by

```
2P_s(1+2W_s/Q_s)
 = O(M/r² + W/(Mr) + 1/M).
```

Summing the two geometric series and the at-most-k rounding terms gives **O(M+W/M)**; k/M is absorbed by O(M). Total public pair count is O(M). These assertions are upper bounds and do not claim Θ(M) genuine root lifts for an arbitrary W. The explicit pair loop itself is Θ(M) for these rectangles and fixed ℓ, since a constant fraction of each coordinate is a unit. There is no free removal of duplicated tags.

## 2. Exact chart domains and deterministic construction

Fix one stratum, abbreviate U_s,V_s,W_s,m_s,Q_s to U*,V*,W*,m,Q, and write m=ℓ^h. Put a=ceil(2h/5), H=ℓ^a. Then 1≤a≤h, H≤m, and H^5 is a multiple of Q. Take **canonical** unit residues u0,v0 in {1,…,H−1}. Canonical representatives matter for the later coordinate bounds.

The exact integer domains are

```
xlo=ceil((1−u0)/H),       xhi=floor((U*−u0)/H),
ylo=ceil((−V*−v0)/H),     yhi=floor((V*−v0)/H),
u'=u0+Hx,                v'=v0+Hy.
```

Use mathematical floor/ceiling for negative numerators. Discard a chart if either interval is empty. A single y interval covers both signs: v'=0 never occurs because v0 is a unit modulo H. Thus there is no puncture to repair at zero. Splitting into positive and negative y boxes is also valid and changes only a constant factor.

The parent's singleton language needs this interpretation: an interval of integer coordinate values with diameter <H gives at most one point in each residue chart. In particular H>V* alone does **not** imply singleton signed-v charts. For H=3,V*=2,v0=1, that chart contains −2 and 1. H>2V* is a sufficient condition for singleton charts on the combined signed interval; alternatively apply the singleton statement separately to the two signs. No root or coverage argument fails when this is specified correctly.

For a fixed residue chart, testing whether 4Nu0v0 is a square modulo ℓ costs O(1) modular trials because ℓ is fixed. If it is nonsquare, discard the chart. This discards no rooted point: u',v' have the same reductions modulo ℓ as u0,v0, and a unit is a square modulo an odd prime power exactly when its reduction modulo ℓ is a square.

If it is square, choose one root modulo ℓ and lift it to r0 modulo Q. An explicit one-digit step from a_j²≡D (mod ℓ^j), D=4Nu0v0, is

```
d_j = ((D−a_j²)/ℓ^j) · (2a_j)^(−1) (mod ℓ),
a_(j+1)=a_j+ℓ^j d_j,       0≤d_j<ℓ.
```

The division is exact, the inverse is a unit, and j runs to 2h−1. Using the integer D or a fixed representative modulo Q is harmless at these precisions. This supplies a deterministic poly(log N+log M) construction, with O(h) lift steps as a simple sufficient implementation. It does not need a factorization or square root modulo N. A constant number of modular inverses modulo Q then constructs all 15 coefficients. The number of arithmetic operations per *root lift* is not a constant; its bit cost is polynomial logarithmic.

## 3. Quartic identity and all root signs

Let c_i=binom(1/2,i), so

```
(c0,c1,c2,c3,c4)=(1,1/2,−1/8,1/16,−5/128).
```

Define the rational polynomial

```
P4(A,B)=Σ_(i+j≤4) c_i c_j A^i B^j.
```

In Z[1/2][A,B], every monomial of `P4(A,B)²−(1+A)(1+B)` has total degree at least 5. One proof takes the product of the two formal square-root series and observes that truncation does not alter coefficients through degree 4. This is a finite coefficient identity through degree 8, so no analytic convergence assumption is needed. Half-binomial coefficients have only powers of 2 as reduced denominators; the displayed finite list already suffices here. Do **not** implement them by inverting i! modulo Q when ℓ divides i!; reduce the rational coefficient first.

Substitute A=Hx/u0, B=Hy/v0 in Z/QZ. Both coordinate inverses exist modulo **Q**, not just modulo ℓ or m. Every error monomial contains H^5 and vanishes modulo Q. Consequently the polynomial with coefficient representatives

```
R(x,y)=Σ_(i+j≤4) d_ij x^i y^j,
d_ij = r0 c_i c_j H^(i+j) u0^(−i) v0^(−j) mod Q,
0≤d_ij<Q,
```

satisfies `R(x,y)²≡4N(u0+Hx)(v0+Hy) (mod Q)` for every integer x,y, including negatives. Reducing each coefficient first preserves polynomial evaluation modulo Q. R≡r0 modulo ℓ, so R is always a unit. The roots R and −R are distinct modulo Q and exhaust all roots. If a covered S lies at the point, there is therefore exactly one sign σ∈{+1,−1} with S≡σR modulo Q. Both sign branches must be retained. A base root need not be the least positive root, and the chart base need not itself lie inside the coordinate intervals.

This proves the claimed absence of a per-pair root or carry oracle. It does not prove that the eventual product over those pairs can be evaluated cheaply. Small h or vanishing coefficients can lower the actual degree; “degree at most 4” and the conservative 15-term bound remain valid. A separate Lean proof of this identity would certify only that identity, not chart acquisition, full coverage, or bit complexity.

## 4. Common lift interval, nonzero guard, and leaf interface

For each nonempty chart choose the integer

```
Z=max(1,|xlo|,|xhi|,|ylo|,|yhi|),
B=Rmax=15QZ^4,
K=ceil((W*+B)/Q),      −K≤τ≤K.
```

There are 15 monomials of total degree ≤4 and Z≥1, so |R(x,y)|≤15QZ^4=B. For every true S with |S|≤W*, the exact integer τ=(S−σR)/Q satisfies |τ|≤(W*+B)/Q≤K. Thus the common interval covers it, with all endpoints and negative indices intact. Empty coordinate charts contribute no product; singleton coordinates or K=0 have the usual one-point meaning. In this particular conservative choice B/Q≥15, K is positive even if W*=0.

Every represented value S'=σR+Qτ obeys

```
|S'|≤B+QK≤W*+2B+Q.
```

The integer exponent

```
E=u0+Hx+N(v0+Hy)−σR(x,y)−Qτ
```

is a polynomial of total degree ≤4, linear in τ. Since |v'|≥1, `|u'+Nv'|≥N−U*`. Hence the specified strict, exactly checkable guard

```
U*+W*+2B+Q<N
```

ensures E≠0 for **every** leaf, including extra lifts. E is positive when v'>0 and negative when v'<0. For a true S=u'p+v'q one has `E=(p−1)(v'q−u')`, giving a nonunit leaf 1−alpha^E for every unit alpha. This is precisely the coverage input to W020. A full internal product gcd is not an annihilator; first localize a nonunit leaf, then use its actual nonzero integer E and the original uniform alpha. The accepted ≤2 expected-trial result still requires a complete covered schedule and the W020 input promises. No high-order step or global-tag recovery is reinstated.

Chart records consist of s,u0,v0,σ,Q,H, the fixed coefficient array, and interval endpoints. They are constructible using public binary inputs. For example,

```
|E|≤U*+NV*+W*+2B+Q.
```

All coefficient, endpoint, index and exponent widths are O(log N+log M+log(W+1)) here, using U,V<M and the canonical representatives; they are O(log N) when M,W=N^O(1). Modular powers must use binary exponents and an inverse for negative powers after alpha's unit check. E is not reduced modulo Q, N, or an unknown order. A numerical loop of length |E| is not the claimed cost model.

Ordinary box restrictions are exact: halve an integer interval, retain the same polynomial and sign, and multiply the two child products. Retain the original guard and B on descendants. Halve the finite chart list as well; the total depth is O(log(number of charts)+log(maximum box cardinality)), hence O(log N) in the displayed regimes. A singleton reveals u',v',τ,E with polynomial bit work and no root search. These facts give a workable restriction/decoding *representation*. They do not supply or amortize the product evaluator at every visited node. A future evaluator must handle these subsets with its stated cost; rebuilding per restriction, chart setup, and exponent setup cannot be silently dropped.

## 5. Balanced costs: the displayed powers are correct

Assume **U,V=Θ(sqrt M)** with fixed constants, canonical residues as above, and choose the ordinary public bound W=Θ(sqrt(MN)); an O-bound suffices for the upper estimates. Constants may depend on fixed ℓ and the balanced-range constants. Writing r=ℓ^s, nonempty strata satisfy r≤min(U,V)=O(sqrt M), and

```
H_s=Θ((M/r)^(2/5)),
P_s=O(M/r²),
C_s≤min(H_s,U_s) min(H_s,2V_s)≤H_s²,
Z_s=O(1+sqrt(M)/(r H_s))
   =O(1+M^(1/10)/r^(3/5)).
```

Here C_s counts chart domains before the harmless constant-factor sign and quadratic-residue filter. Scanning canonical residues costs O(H_s), also summed and paid. For sufficiently large M the top balanced intervals contain every residue modulo H; exactly half of unit residue pairs have a square radicand modulo ℓ. Thus the explicit top chart list really has Θ(H²)=Θ(M^(4/5)) rooted charts, not merely an upper bound inferred to be a lower bound. Total chart acquisition across strata is O(M^(4/5) polylog N), with its actual deterministic construction included.

The common lift length in stratum s is

```
T_s=2K_s+1
   =O(1+W_s/Q_s+Z_s^4)
   =O(1+Wr/M²+M^(2/5)/r^(12/5)).
```

Its ordinary-width part **increases** like r; it is only after multiplication by the smaller pair count that the occurrences decrease. Multiplying by P_s gives

```
O(M/r² + W/(Mr) + M^(7/5)/r^(22/5)).
```

Thus total chart occurrences, including all extra lifts and both signs, are

```
L=O(M+W/M+M^(7/5))
 =O(M+sqrt(N/M)+M^(7/5)).
```

The added envelope relative to canonical lifts is O(M+M^(7/5)); the lower-stratum added envelope is exactly the claimed `O(M/r²+M^(7/5)/r^(22/5))`. The denominator 22/5 comes from 2+4·3/5. At the top, `Rmax/Q=O(1+M^(2/5))` and `T=O(1+sqrt(N)/M^(3/2)+M^(2/5))`.

Carry enlargement is within the *chosen ordinary width scale* when

```
M^(2/5)≤sqrt(N)/M^(3/2)
⇔ M^(19/10)≤N^(1/2)
⇔ M≤N^(5/19),
```

up to fixed constants and the additive 1. If only W=O(sqrt(MN)) is assumed, one may compare these upper envelopes, but cannot conclude that enlargement is dominated by the *actual* W for an arbitrarily smaller supplied bound. Choosing the usual Θ-scale bound removes that ambiguity. The same comparison is easier in lower strata, by the additional r^(17/5) in the denominator of the ratio.

The guard also holds eventually throughout this balanced regime, not just the counting estimates. Uniformly in strata,

```
Rmax_s=O(M²/r²+M^(12/5)/r^(22/5)),
U_s+W_s+2Rmax_s+Q_s
 =O(sqrt M+sqrt(MN)+M²+M^(12/5))=o(N)
```

for M=O(N^(5/19)). The largest displayed powers at that endpoint are N^(12/19). Exact checking plus a fixed finite-small-N fallback is legitimate under these fixed balanced constants.

At M=Θ(N^(1/4)), all the quoted exponents check: H∼N^(1/10), chart list Θ(N^(1/5)), Z=O(N^(1/40)), ordinary τ width ∼N^(1/8), carry τ term O(N^(1/10)), explicit pair enumeration Θ(N^(1/4)), genuine-width occurrence envelope O(N^(3/8)), and extra occurrence envelope O(N^(7/20)). Acquisition alone reaches the numerical one-fifth exponent for this explicitly listed chart representation. That statement is not a lower bound on acquiring a more compressed representation.

## 6. Unbalanced ranges are a substantive separate obligation

The chart construction and coverage proofs above hold for all admitted U,V. The small balanced Z estimate does not. In general use

```
Z_s=O(1+max(U_s,V_s)/H_s),
C_s≤min(H_s,U_s) min(H_s,2V_s).
```

One need not materialize U+V individual coordinate roots: enumeration of residue representatives modulo H constructs these charts directly. Thus the old coordinate-root `U+V` acquisition cost is **not forced by this particular new representation**. The difficulty persists in its longer coordinate domains and larger common lift intervals.

For example, in an allowed thin rectangle U=Θ(M), V=Θ(1) with W=Θ(sqrt(MN)), the top stratum has Z=Θ(M^(3/5)), C=O(M^(2/5)), and the **specified conservative bound** B=15QZ^4 is Θ(M^(22/5)). Its additional occurrence envelope is O(M^(17/5)), and keeping the carry term within the ordinary-width scale would require M≤N^(5/39). At M=Θ(N^(1/4)) this B grows as N^(11/10), so the proposed strict guard fails for all sufficiently large N in such a range. This demonstrates failure of this guard/enclosure there; it does not prove that an actual E=0 leaf must exist or that every tighter enclosure fails.

A finite-small-N fallback cannot repair a growing unbalanced family. One must supply a different range schedule, tighter/anisotropic chart construction, smaller exact lift representation, or a fallback with its full asymptotic cost. Inherited W019 small-factor preprocessing and every remaining dyadic range remain real costs. No balanced-only count is a complete factoring theorem.

## 7. Generic dense shift blocks: b^40 and b^70 are the right envelopes

For one fixed chart/sign, write its exponent as a bivariate quartic f(x,y) plus the linear term −Qτ. Translate x=bk+i, y=bl+j, with 0≤i,j<b. The homogeneous degree-4 part in local i,j is independent of k,l,τ and can be absorbed in the factor coefficients. The remaining local monomials i^α j^β of total degree d=α+β≤3 number d+1 for each d. Use one variable for the alpha-power of each corresponding translated coefficient, including the constant monomial. Thus there are 1+2+3+4=10 variables before digit splitting.

For a microblock of b² leaves, the individual degree of a variable attached to a degree-d local monomial is at most, and in the unreduced generic box scales as,

```
Σ_(0≤i,j<b) i^α j^β = Θ(b^(d+2))    (b≥2, 0^0=1).
```

The dense rectangular storage envelope is therefore

```
Π_(d=0..3) b^((d+1)(d+2)) = b^(2+6+12+20)=b^40.
```

If the polynomial must work universally for all chart coefficient arrays, the five degree-4 local monomials also become variables. Their contribution is b^(5·6)=b^30, producing **15 variables and b^70 slots**. This particular universal block polynomial is coefficient-independent and really can be shared, but its acquisition/storage and all evaluation points still cost work. Relations among the special coefficients, cancellations, or another representation might avoid these boxes; no actual-support lower bound is being asserted.

To apply the accepted composite-ring evaluator in W021 at these envelopes, digit-split **after** constructing the product: the 10 unequal-degree variables become 40 fixed variables of individual degree O(b), and the universal version becomes 70. Merely citing the rectangular volume with unequal degrees is insufficient for a theorem parameterized by the maximum individual degree. The fixed-dimension Turing-machine theorem and its ε-dependent constants are imported from the accepted W021 interface, not re-proved here. Degree-aware product trees give the same soft construction envelope for this dense representation; at a node of n factors each original variable degree is O(n b^d), and the last levels dominate. All exponent and evaluation-point widths remain paid.

With τ enumerated, a chart with comparable coordinate side lengths Θ(Z) has O((1+Z/b)²T) outer records. The abbreviated Z²T/b² form requires b≤Z and regular block handling. Edge strips or a finite set of rectangular block shapes must be paid, as must singleton/short charts; simply dropping them loses coverage. Blocking τ too multiplies the degrees by its block length and introduces its progression dependence. The two-dimensional b^40/b^70 formulas cannot be reused unchanged.

Even ignoring these extra costs, the quoted dense composition does not reach the target. A per-chart envelope `b^40+Z²T/b²` balances at b=(Z²T)^(1/42), giving `(Z²T)^(20/21)` before ε and width factors, if it fits the sides. At M∼N^(1/4), Z²T∼N^(7/40) and multiplication by Θ(N^(1/5)) charts gives **N^(11/30)**. A shared universal dense envelope `b^70+L/b²` balances to L^(35/36), which at L∼N^(3/8) gives **N^(35/96)**. Both exceed N^(1/5) by a wide margin. These are diagnoses of the charged dense approach, not optimality theorems or certified implementations of the omitted boundary work.

There is an additional useful target distinction. Even a hypothetical square-root evaluator applied separately to every balanced chart would cost about

```
C sqrt(Z²T) ∼ M^(4/5) sqrt(sqrt(N) M^(−13/10))
           = N^(1/4) M^(3/20),
```

when the ordinary width dominates. Improving only the per-chart kernel to that scale does not suffice. Work must be shared across charts, or the number/shape of charts must change.

## 8. Focused prior-art scope and next computation

Harvey–Hittmeir's Proposition 3.3 already uses short lattice weights with a stationary congruence modulo an arbitrary m coprime to N to determine a weighted sum modulo m². This is close prior context for the coverage mechanism; its statement allows composite m. It does not supply this quartic-chart product evaluator. [Harvey–Hittmeir, §3, Proposition 3.3](https://arxiv.org/html/2105.11105v1#S3).

Valuation reduction and Newton/Hensel acquisition of unit square roots are standard constructive tools; Caruso §1.2.3 discusses those computations and the difference between odd primes and 2. The finite quartic identity and the cost calculations above are proved directly here. Neither elementary chart construction nor the bounded source check supports a novelty claim. [Caruso, *Computations with p-adic numbers*, §1.2.3](https://jncf2017.lip6.fr/files/lecture-notes/jncf2017-caruso.pdf).

The [source record](W022-primepower-charts-review-evidence/source-retrieval.json) retains queries, fetched sources, hashes, exact read scope and a failed unused Conrad URL. There was no broad literature survey. The completed W021 review supplies the accepted composite-ring Turing-machine evaluation interface; its certificates were not rerun.

**Disposition: revised/accepted representation; no complete algorithmic improvement.** The next useful computation is an exact, public, **batched** evaluator/localizer for

```
Π_(strata, rooted charts, σ=±1)
  Π_(x∈Ix, y∈Iy, −K≤τ≤K) (1−alpha^(u'+Nv'−σR(x,y)−Qτ)) mod N,
```

or an equally covering collision representation, without expanding Θ(M) pairs or the full common-lift occurrence set. Exploit the square-root coefficients and the linear τ progression with a stated algorithm, actual degrees/storage, paid coefficient acquisition, and cost-preserving chart/box restrictions. A formula for the scalar product alone is insufficient. It must also preserve the nonzero guard or supply another proved treatment of every zero exponent.

For a concrete **conditional target**, an aggregate cost Õ(C+sqrt L), including localization and binary setup, would balance the balanced chart bill M^(4/5) with the original width/small-factor bill (N/M)^(1/4) at M∼N^(5/21), giving a balanced bookkeeping exponent 4/21. This is a specification for a missing computation, not evidence it exists, and it still leaves the unbalanced ranges above unresolved. The b^40/b^70 approach supplies no such bound. No additional certificate of the already-proved quartic identity would discharge these algorithmic obligations.

Only this report and its evidence directory were written. No delegation, installs, commits, solver/Lean/STATE/registry/task-file changes, numerical runs, parameter sweeps, or shared-code checks occurred. [Verification](W022-primepower-charts-review-evidence/verification.json) and the [delivery manifest](W022-primepower-charts-review-evidence/delivery-manifest.json) record the final evidence boundary.

At handoff all frozen input hashes and the brief hash matched. Live `docs/SPECIFICATION.md` and `research/STATE.md` had changed; their new contents were not substituted into this review. W022 and all four imported findings remained identical to the frozen versions.
