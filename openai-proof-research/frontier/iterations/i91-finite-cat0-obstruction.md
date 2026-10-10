# I91 — original prerequisite audit and a finite CAT(0) inequality certificate

Date: 2026-10-10. Premise pin: **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb**.

**Original prerequisite verdict: ORIGINAL PASS WITHOUT REPAIRS** for original I89 F89, Lemmas 3.1 and 3.2, their normalization and limiting estimates, equations (4.1)–(4.4), and the actual rooted-tree counterexample. R89/H89/E89 are **NOT INDEPENDENTLY REVIEWED HERE**. This verdict is an analytic review of the original bytes, not an inference from the parent's evidence replay.

**New author result:** Q89's finite uniform energy-contraction assertion is proved below by fixed-scale estimates followed by a retained exact rational inequality certificate. The constants are specified, extremely inefficient rationals. No compactness constant, unexecuted search termination, numerical optimizer, or assumed approximate splitting is used in this result. The geometric lemmas and their reduction to the certificate are author proofs requiring independent review; exact certificate verification does not independently review that analytic reduction.

**Contribution disposition: no substantial finding nominated or count increment.** This is a completed finite bridge for review, but its contribution is not cleared: extraction of explicit constants from accepted rigidity operations may be technical. The bounded comparison below identifies the classical ingredients and the accepted operations actually reused. Eight findings remain accepted. No worldwide priority claim is made. No literal finite hyperbolic presentation has been output; the explicit finite-enumeration interface and that unperformed obligation are separated in §7.

## 1. Inputs, review scope, and notation

Only this report and `frontier/{sources,experiments}/i91_finite_cat0_obstruction/` are owned. The four live ledgers were snapshotted; only `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift. AGENTS.md, original I89 files, finalized parent replay, I79 domain and seals, and used source bodies are immutable references. No shared edit, staging, commit, publication, or delegation occurred. I90 is independent.

Write **A** for the exact pinned directory

`preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/`.

Its TeX is reused under `frontier/sources/i14_spectral_width_novelty_r3/corpus/`; its original PDF and extraction are reused through I79. All seven `build/sections/01-introduction.tex` through `07-completion.tex` were read in full, including the diagram normalization/weighted-rank/separator operations, star coupling normalization, energy operations, exceptional incidence, direction semicircle, and parallel-set argument. Source truth is stipulated, including lower operations; this review tests the added deductions and applicability. Exact file, line, label, passage and byte bindings are in `passages.json` and `immutable-references.json`.

Original report SHA-256: `29adb44728edee78ef949c390de75cb9c486da8860bcf7817898f132bb4f86be`. Original seal SHA-256: `4d9c2b12ad1bc77dd8c313164e62cc9c9ed80aab1bce82f8cd60de33225a0583`. The original report is not amended by any new argument below.

The actual template has 18 core vertices, 32 core fields, seven fans of sizes 6,6,6,4,3,3,3, 90 decoration squares, 212 master fields and 98 required entries. In the executable naming convention, A=1, B=2, C=4, D=7 in the nonzero binary vectors 1,…,7; a line through i,j is `{i,j,i xor j}`. `X1,Y1` represent A, etc. `L123` denotes the line {1,2,3}. The missing edge is `Y7--L347`, and `X7--L347` is loose. No altered incidence configuration is substituted.

Distances below are those in A's finite product over matches, with squared metric equal to the average squared factor distance. This is a complete CAT(0) space even when action spaces are nonproper or infinite dimensional. Write `[u,v]_s` for the point at fraction s, and `mid(u,v)=[u,v]_(1/2)`. All auxiliary points used below exist in this finite product. We never assume geodesic extendibility.

## 2. Independent audit of ORIGINAL I89

### 2.1 Lemma 3.1: ORIGINAL PASS

For a finite symmetric alphabet with multiplicities, distance convexity along `(y_t,sy_t)` gives convexity of E. Continuity follows from the finite sum. The functional `F=E+lambda d(o,.)²` has the midpoint deficit `lambda d(y,z)²/4`. If `F(y_n)` decreases to its finite infimum, that deficit makes the minimizing sequence Cauchy: `lambda d(y_n,y_m)²/4` is at most the mean excess of its two values above the infimum. Completeness gives the minimizer, continuity gives attainment, and the same deficit gives uniqueness. This requires neither properness nor compactness of a bounded ball.

The derivative direction in the original proof is valid. For sufficiently small t, A's crossed-geodesic inequality and alphabet symmetry give

`F(p) <= F(p_t) <= average_s d(p_(2t),sp)² + lambda d(o,p_t)²`.

The outer expressions agree at t=0. Their right derivative is therefore nonnegative. First variation gives `-4 average<h,log_p(sp)> -2lambda<h,log_p(o)> >=0`. Bounding the last scalar product by its norm gives precisely the original coefficient `lambda/2`. Represented directions are dense in the completed tangent cone; scalar products with the finitely many fixed vectors are continuous. This is a cone argument, not a Hilbert gradient calculation.

After scaling by `E(p)^(-1/2)`, the original b is correct. In fact, when `E(p)>E(o)/4`, comparison with o gives

`b² <= lambda(E(o)/E(p)-1)/4 < 3lambda/4 <= lambda`.

Thus its weaker `b<=1/k` at `lambda=k^-2` is valid. The six-letter displacement proof in A, `energy:displacement-bound`, uses normalization and relations only; its hypotheses do not include energy minimality. Hence `M=6` follows from `25(1+1/10)/(1-1/10)=275/9<36` at the proximal point. This applicability check is essential to the arbitrary-action extension.

### 2.2 Lemma 3.2: ORIGINAL PASS

The defect variance inequality is the cone cosine identity summed over letters. Conditional on the previous inductive mean u, independence of the next *uniform* letter and `||u||<=M` gives

`j² a_j <= (j-1)² a_(j-1)+1+2bM(j-1)`.

Summing from 2 to t gives `t²a_t<=t+bM t(t-1)`, with the t=1 endpoint included. Cone scalar-product concavity has the required direction: the average pairing with the leaves is at most the pairing with their inductive mean. Under the coupling, the value h_I is common to the branches because the I-labels agree exactly. It may depend on all the leaves. Only its norm bound is used in the last pairing estimate, so no extra independence is inserted.

With A's convention `TV=(1/2) sum|p-q|`, the errors `2M²eta` and `2BM eta` are valid conservative bounded-function estimates. One is for the leaf distribution of the squared mean norm; the other is for each branch's signed scalar-product test. Fixed inversion preserves uniformity because the alphabet is symmetric with its multiplicities. The resulting original (3.3) is correct with both errors present.

### 2.3 F89 and its quantifiers: ORIGINAL PASS

Negating the statement as written gives, for every integer k>=10, some j_k>=k and an action/basepoint violating contraction at lambda=k^-2. There is no need for j_k to be strictly increasing: j_k→infinity suffices. For each fixed test and fixed t, both table errors tend to zero, and the defect term tends to zero. The upper limit is at most B/sqrt(t); t tends to infinity only afterward. Paths use B<=12 and the ternary midpoint uses B<=6.

Reading all of A's `05-energy.tex` confirms that, after its minimizing-basepoint lemma has supplied the stationary test, the remaining operations require only that test, normalized bounded displacements, and the table statistics. Thus replacing that input by the original limiting defective test is valid. This does not apply the printed `prop:configuration` beyond its hypotheses as a black box: it reuses its complete lower proof. Products and ultralimits are complete CAT(0) without a properness or dimension restriction. Every fixed fractional-point inequality passes first; the angle is computed afterward in the limit. The exact no-configuration operation in `06-obstruction.tex` then applies as stipulated.

The iteration sum is `sum_(n>=m) K 2^-n sqrt(E(o_0))=2K2^-m sqrt(E(o_0))`. Every generator of the fixed alphabet has displacement at most `sqrt(|S_j|E(o_m))`, which tends to zero; continuity gives a common fixed point. Here j and its finite alphabet are fixed before m increases. The infinitude, hyperbolicity and finite two-dimensional aspherical model are supplied by A. The torsion-free consequence uses the finite-length free cellular resolution restricted to a finite cyclic subgroup; that subgroup's integral cohomology in arbitrarily high even degrees excludes torsion. No quantitative sequence threshold is obtained by this audit.

### 2.4 Original finite errors and tree: ORIGINAL PASS

With `a=2M²eta_0`, edge squares lie in `[1-a,1+a]`. The log-comparison path induction subtracts `2tau` at each step after the first, giving `k-ka-2(k-1)tau`. The three terms inside the original conditional square root each cost at most `tau²/(16B²)`, and the outer term costs at most tau/4 under the specified budget. Their total is `(sqrt(3)+1)tau/4<tau`.

For a decoration square, side-square sum <=4+4a and both diagonal squares >=2-2a-2tau give the upper diagonal `2+6a+2tau` and midpoint-square bound `2a+tau`. For the hexagon quadrilateral, the side sum is <=6+14a+4tau; subtracting one opposite lower bound `3-3a-4tau` gives `3+17a+8tau`. Subtracting both and dividing by four gives `5a+3tau`. These are the original report's §4 estimates, following its §3 normalization/test estimates; all pass as originally written.

The actual compact real tree consists of a stem of length epsilon and two terminal branches of length 1-epsilon. Its root-to-leaf distances are 1 and its leaf distance is 2-2epsilon. Initial segments of length <epsilon coincide, so the root angle is exactly zero. At equal fraction s the distance is `2 max(s-epsilon,0)`. These statements hold in complete CAT(0) spaces realized by actual trees. They refute root-angle continuity from fixed-scale endpoint distances; they do not refute Q89. No repaired original claim is substituted.

## 3. Q91: specified finite contraction parameters

Put

```
e_*    = 10^(-80032),          tau_* = e_*/2,
theta  = 1/10,
eta    = e_*^2 / 663552,
lambda = e_*^4 / 55296^2,
T      = 9216 * 10^160064.
```

These are rational numbers and a specified integer, not asymptotic placeholders. Powers of ten denote exact integers/rationals.

**Theorem Q91 (author proof).** Let a finite realization of A's actual tables have nonempty master-match set. Suppose every single-field marginal is within TV eta of uniform, and every admissible common-I coupling for `1<=t<=T` exists with every branch marginal error and its joint leaf-law error at most eta. Suppose the six-letter pair counts have relative error at most theta, as in A's `sample:eq-six-pair` (positions 1,k suffice). Impose A's fan, top, and decoration relations. For every isometric action of the resulting group on every nonempty complete CAT(0) space, and every x,

`E(J_lambda x) <= E(x)/4`.

Energy uses the original finite symmetric alphabet with multiplicities. No asphericity, hyperbolicity, properness, local compactness, finite dimension, or presentation-size bound is assumed in this statement.

*Reduction to geometry.* If contraction fails, normalize at the proximal point. The audited lemmas give M=6, B=12, and `b<=sqrt(lambda)=e_*²/55296`. With `tau=tau_*`, the paid sufficient conditions are exactly

```
t >= ceil(16 B²/tau²),
b <= tau²/(16 B² M),
eta <= min(tau²/(32 B² M²), tau/(8BM)).
```

Our T equals the first bound, and eta equals the first term in the final minimum and is smaller than the second. Also `a=72eta=e_*²/9216`, hence `e:=a+tau<=e_*`. All path and ternary conditional tests consequently have upper pairing bound tau. Section 4 constructs finite points whose squared distances satisfy the perturbed linear system of §5 with error at most `2000e^(1/8)`. This is less than `10^-10000` because `80032/8=10004`. Section 5 proves that system inconsistent at that error. This contradiction proves the theorem. The E(x)=0 case follows directly from proximal minimality. ∎

The usual energy iteration then has geometric convergence to a fixed point and the distance estimate `2 lambda^(-1/2) 2^-m sqrt(E(x))`. This last step is classical and is not another contribution.

## 4. Approach I: fixed-scale geometric propagation

Here are full analytic bounds connecting the actual product configuration to the finite certificate. Assume `0<e=a+tau<=2^-32`; the theorem uses a much smaller value. Core edges have squared error at most e, two-step squares differ from 2 by at most 6e, and opposite squares in a core hexagon differ from 3 by at most 17e. The stronger asymmetric bounds from the original audit remain available. No tangent cone at a hexagon center is taken.

### 4.1 Nearby centers, fan midpoints, and finite fractions

The three opposite-pair midpoints in any one core hexagon have mutual distance at most `sqrt(5e)`, by applying the original quadrilateral estimate in the three cyclic positions. Construct the graph of core hexagons, joining two when they share an opposite pair. Exhaustive enumeration of the noncollinear unordered triples in F_2^3 and all permitted X/Y choices gives **86 hexagons**, and breadth-first searches from every one give **diameter 3**. This is a finite exact combinatorial calculation, reproduced by `template.py`; it enumerates all 28 noncollinear triples and filters the missing incidence. Alternatively A's basis-change and Y-replacement proof gives connectivity; the diameter is the finite extra calculation used here.

Choose c to be one opposite midpoint in the first hexagon in canonical order. Across an adjacency the two chosen centers are within `2sqrt(5e)`. Thus every opposite midpoint of every hexagon is within `7sqrt(5e)<=h:=21sqrt(e)` of c. Every core vertex lies in a hexagon. Since its distance to its opposite midpoint is half the opposite distance,

`|d(c,z)²-3/4| <= R := 17e/4+3h`                 (4.1)

for every core vertex z. The factor 3 bounds the sum of the two radial distances; h<=1/4 and the opposite half-length is <=1 here.

For i=A,B,C,D let `J_i=mid(X_i,Y_i)`. For any distinct full lines H,H' at i, the square `(X_i,H,Y_i,H')` has sides with squared error <=e and diagonals with the original lower bound 2-2e. Its two midpoint distance is therefore at most

`s:=sqrt(2e)`, so `d(J_i,mid(H,H'))<=s`.          (4.2)

The actual ternary conditional test gives, with H=CD, J=J_C and z=X_D, **for every fixed u,v in [0,1]**,

`d([H,J]_u,[H,z]_v)² >= u²d(H,J)²+v²d(H,z)²-2uv tau`. (4.3)

Indeed in each factor the vector toward J is a function of the same two F_C fields, has norm <=6, and the third vector uses the loose field. Coordinatewise fractional points multiply the logarithms by u,v before averaging. No independence of the common conditioning tuple is needed. The proof below only needs (4.3) at u=v=1; the fractions 1/3 and 2/3 introduced later are actual geodesic points, controlled by convexity. This finite route therefore avoids any interchange of angle and limit.

### 4.2 A quantitative reverse-median inequality

We use the CAT(0) Reshetnyak inequality in its equivalent Young form, valid for every q>0:

`d(p,j)²+d(z,c')²-d(p,c')²-d(z,j)² <= q d(p,z)²+q^-1 d(c',j)²`. (4.4)

This follows from the metric Cauchy–Schwarz bound by `2uv<=qu²+q^-1v²`. The exact primary statement is given by Berg–Nikolaev, *A K-quadrilateral cosine characterization…*, arXiv:1512.01736v1, Introduction pp.1–2, displaying the K=0 quadrilateral cosine formula and recalling their 2008 characterization. It holds in arbitrary CAT(0) spaces, with coincident-point cases obtained directly or by continuity. This is a classical input, not a newly asserted all-curvature theorem.

**Reverse-median lemma.** Suppose `c'=mid(p,w)`, `j=mid(z,w)`, and the four squared distances `d(p,w)²,d(z,w)²,d(p,z)²,d(z,c')²` differ respectively from `3,2,1,3/4` by at most epsilon<=1/16. Then

`|d(c',j)²-1/4| <=2sqrt(epsilon)`.

*Proof.* Put P=d(p,w)², D=d(z,w)², A=d(p,z)², Z=d(z,c')² and x=d(c',j)². Midpoint convexity gives `d(p,j)²>=2x-D/4+P/2`. Substitute into (4.4), using `d(p,c')²=P/4` and `d(z,j)²=D/4`, to obtain

`(q^-1-2)x >= Z+P/4-D/2-qA`.

Take `sigma=sqrt(epsilon)`, `q=1/2-sigma` (the zero-error case follows by sigma↓0). The right side is at least `1/2-q-(9/4)epsilon`. Since `q^-1-2=2sigma/q`, this yields `x>=1/4-(17/16)sqrt(epsilon)`. Busemann convexity for the two segments ending at w gives `x<=A/4<=1/4+epsilon/4`. These prove the claim. No exact flat triangle or differentiability is used. ∎

Apply this lemma to a pair H,H' of full lines at i in a common core hexagon, with w=H, z=H', and p opposite H in that hexagon. Here d(p,H')² is an edge square. Their actual opposite midpoint c' is within h of c, so all four errors are bounded by

`E0 :=17e+R+3h`.

The lemma bounds the radius of `mid(H,H')` relative to c'. Transfer its basepoint by h and its midpoint by s using (4.2). All distances involved are bounded by 2, and the squared-distance transfer costs at most `5(h+s)`. Consequently

`|d(c,J_i)²-1/4| <= F:=2sqrt(E0)+5(h+s)`.        (4.5)

The simpler direct convexity upper bound `d(c,J_i)²<=1/4+R+3e/2` will also be useful. The assumptions h<=1/4, E0<=1/16 and the bounded-distance conditions hold for e<=2^-32. These are explicit numerical smallness conditions, independent of the action.

### 4.3 Exceptional incidence without a sector identity

Continue to write H=CD, J=J_C, z=X_D. From (4.2),

```
|d(H,J)²-1/2| <= U:=3e/2+3s,
|d(J,z)²-3/2| <= L:=U+8e.
```

For the second assertion the lower bound follows from (4.3) at (1,1) and `d(H,z)²>=1-e`. Its error is at most U+3e. The upper bound follows by midpoint convexity from the two-step distances X_C--X_D, Y_C--X_D and X_C--Y_C; it is at most `3/2+15e/2`.

Let `B0=[J,z]_(1/3)` and `q=[c,H]_(1/3)`. Squared-distance convexity, retaining the negative term `-(2/9)d(J,z)²`, gives

```
d(c,B0)² <= 1/12 +R+e+2L/9,
d(H,B0)² <= 1/3 +2U/3+e/3+2L/9.
```

Apply convexity once more to q and the point B0, using `d(c,H)²>=3/4-R`. The constant terms cancel exactly, leaving

`d(B0,q)² <= V:=8R/9+7e/9+2U/9+2L/9`.          (4.6)

Thus the exceptional incidence yields a quantitative **finite-distance collinearity relation**, with error sqrt(V) tending to zero. It is not a statement about the root angle. B0 need not lie exactly on cH, and no linear addition of cone vectors has been assumed.

### 4.4 Near-antipodality as a finite midpoint statement

Put y=Y_D, K=J_D. The admissible path `Y_D,AD,X_D,CD` gives `d(y,H)²>=3-4e`; the triangle inequality through c gives `d(y,H)²<=3+4R`. This missing-incidence pair is **not** a hexagon opposite pair. Let `c'=mid(y,H)`. Midpoint convexity gives

`d(c,c')<=r0:=sqrt(R+e)`.

Put `f'=F+3r0`, so `|d(c',K)²-1/4|<=f'`. Since K=mid(z,y), `d(y,K)²=d(z,K)²` differs from 1/2 by at most 3e/2. Convexity at c' and at K, respectively, gives

```
d(H,K)² >=3/2-2f'-4e,
d(H,K)² <=3/2+2R+2e.
```

For clarity, we justify the fixed-fraction lower estimate used next. If `w_t=[y,H]_t`, then

`g(t)=(1-t)d(K,y)²+t d(K,H)²-t(1-t)d(y,H)²-d(K,w_t)²`

is a nonnegative concave function with g(0)=g(1)=0: subtract strong squared-distance convexity from the quadratic interpolant. Concavity and the endpoint values imply `g(t)<=2g(1/2)` for every t. The bounds above give `g(1/2)<=f'+R+3e`. At `q'=[y,H]_(2/3)=[c',H]_(1/3)`, substitution therefore gives

`d(K,q')² >=1/2-4f'-3R-10e`.

By (4.6) and endpoint convexity, `d(B0,q')<=w0:=sqrt(V)+r0`. The distances from K are bounded by 2, so using the conservative squared-distance loss 5w0,

`d(K,B0)² >=1/2-4f'-3R-10e-5w0`.

On the other hand, convexity along Jz gives

`d(K,B0)² <=(2/3)d(K,J)²-1/6+e/2+2L/9`.

Combining the last two inequalities proves

```
1-Omega <=d(J_C,J_D)² <=1+4F,
Omega:=6f'+5R+16e+8w0+L,
d(c,mid(J_C,J_D))² <=F+Omega/4.                 (4.7)
```

The upper bound uses the triangle inequality and (4.5); the last bound is midpoint convexity. Equations (4.1)–(4.7) replace common centers, the needed fan flatness, exceptional-sector collinearity, and C/D antipodality by explicitly vanishing fixed-scale errors. They are valid for the actual product configuration in every complete CAT(0) space.

The remaining transverse parallel-set step is handled by the separate finite inequality approach below. We do not claim that (4.7) by itself supplies an approximate splitting.

## 5. Approach II: an executed rational CAT(0) certificate

### 5.1 The finite terms and their valid inequalities

Take the 18 actual core points, c, and J_A,J_B,J_C,J_D. Adjoin exactly six actual midpoints:

```
u  =mid(AC,J_D),     up=mid(BC,J_D),
v  =mid(AD,J_C),     vp=mid(BD,J_C),
m  =mid(u,v),       mp=mid(up,vp).
```

These are 29 named points and 406 unordered squared-distance variables. They do not assert a transverse factor or a cone dilation. The finite system uses the following ideal specifications, each with an explicit error budget below:

* Core edge squares 1; every core two-step endpoint square 2; every core-hexagon opposite square 3; core radial squares 3/4.
* The four J radial squares 1/4, `d(J_C,J_D)²=1`, and `d(J_C,X_D)²=3/2`.
* c as every core-hexagon opposite midpoint and as `mid(J_C,J_D)`; each J_i as `mid(X_i,Y_i)` and the midpoint of each pair of distinct full lines at i; the six displayed midpoint definitions.

After duplicate removal there are 65 midpoint specifications. At finite error, the repeated descriptions of c and J_i are **approximate**; treating them as exact would be invalid. The errors are paid in §5.3.

For any listed midpoint specification `(n,a,b)` impose the endpoint identities `4d(n,a)²=d(a,b)²=4d(n,b)²` and, for every named z, the midpoint inequality

`4d(n,z)²-2d(a,z)²-2d(b,z)²+d(a,b)²<=0`.

For every four distinct named points impose all three ordinary CAT(0) quadrilateral inequalities. Finally, for each z≠c and each unordered a,b with four distinct endpoints, impose both signs of

`d(c,b)²+d(z,a)²-d(c,a)²-d(z,b)² <= q d(c,z)²+q^-1 d(a,b)²`

for q in `{2/5,1/2,1,2,5/2}`. These are rational instances of (4.4). Normalize each row to primitive integer coefficients without changing its sign; sort by the tuple of variable-index/coefficient pairs. There are **151,892 distinct rows**, maximum coefficient l1 norm **69**. All initial unspecified variables have bounds [0,4]. The bound 4 is valid because all named points lie in the closed radius-one ball about c once e is as small as in Q91; the core satisfies (4.1), and every further point is a midpoint of already bounded points.

`algebraic.py` specifies this complete finite system unambiguously from the actual Fano graph. It is not a semidecision argument about a hypothetical certificate search.

### 5.2 The retained exact contradiction

`certificate.json` contains the initial intervals, 1,687 used rows, and an ordered list of **2,953 bound updates**. Each update isolates one variable in a valid row, substitutes existing lower bounds for positive coefficients and upper bounds for negative coefficients in the other terms, and rounds **outward** to denominator `2^24`. Upper bounds use ceilings and lower bounds use floors. Thus the variables remain arbitrary real squared distances, not dyadic distances.

The resulting bounds make row 85,821 have minimum left side

`186366/16777216 = 93183/8388608 > 1/100`.

The row itself is the midpoint inequality

`d(AC,X_D)²-2d(AC,u)²-2d(X_D,u)²+4d(c,u)²<=0`.

The certified bounds used are respectively `3`, `3/8`, at most `21257015/16777216`, and at least `1237915/16777216`. Their indicated linear combination is the positive margin above. Its right side is zero. This is an exact rational contradiction. `checks.py` independently checks every stored inference using `Fraction`, comparing the rounded result in the correct direction with the unrounded rational bound. It also regenerates the complete row system and original search to bind the retained rows to the stated CAT(0) operations and actual template. This latter regeneration is a semantic/provenance check, distinct from the rational trace verification.

The first exploratory search used inward rounding and is expressly rejected in `preseal-log.md`. Neither its apparent margin nor its trace is used. The corrected certificate above is the one checked and sealed.

### 5.3 Robustness with a specified error, not compactness

Suppose every initial ideal bound is weakened by at most delta in the appropriate direction, and every normalized inequality row is allowed right side delta. An update whose integer coefficient is nonzero and whose row has l1 norm <=69 increases the maximum interval-endpoint error D by at most `delta+68D<=100D`, provided D>=delta. Outward rounding to the same stored ideal endpoint adds no further error: that endpoint already weakens the exact ideal inference. Induction through the retained updates bounds all errors by `100^2953 delta`, conservatively by `100^3000 delta`.

Choose **delta=10^-10000**. In the final row the total loss is at most `69*10^-4000`, and its allowed right side is `10^-10000`. Their sum is less than 1/100. Thus the same finite contradiction holds for this explicitly perturbed system.

It remains to pay that delta from §4. The following coarse envelopes hold for e<=2^-32; only elementary inequalities, not experiments, justify them:

```
h<=21 e^(1/2), s<=2 e^(1/2), R<=68 e^(1/2),
U<=8 e^(1/2), L<=16 e^(1/2), E0<=148 e^(1/2),
F<=140 e^(1/4), V<=67 e^(1/2),
r0<=9 e^(1/4), sqrt(V)<=9 e^(1/4), f'<=167 e^(1/4),
Omega<=1523 e^(1/4), sqrt(F+Omega/4)<=23 e^(1/8).
```

For example `2sqrt(148)<25`, and `25+5(21+2)=140`; the remaining displayed constants follow by substitution. Every ideal squared-distance specification has error at most `1523e^(1/4)`. Each approximate midpoint description is within `23e^(1/8)` of its genuine midpoint, by (4.2), the hexagon-center bound, or (4.7). A change of that size alters a squared distance to any named point by at most four times the size, since both points lie in the radius-one ball. Multiplication by 4 in an endpoint or CN row costs at most sixteen times the size; the conservative allowance **32** times the size is valid. The six new midpoint definitions are exact. All quadrilateral and Young–Reshetnyak rows have zero error.

Consequently all the requirements of the perturbed system hold with

`delta_actual <=2000e^(1/8)`.

At `e<=e_*=10^-80032`, this is at most `2000*10^-10004<10^-10000`. The finite contradiction is therefore paid. This is an explicit finite-distance substitute for the original incompatible tangent scalar products. It establishes Q91 without an approximate line, a parallel-set splitting, or an assumed stability theorem.

The arithmetic certificate proves a universal implication from its finite CAT(0) inequalities. The separate finite tree, recurrence and parameter diagnostics do not prove general geometry. The bridge from actual actions to those inequalities is the full analytic proof in §§2–4, not an inference from sampled metric examples.

## 6. Contribution comparison and evidence limits

The search domain is the complete pinned `sources/preprints-tree.json`: 13,223 entries, 749 manuscripts and 10,373 blobs. It is represented by I79's 9,340 original corpus bodies plus 1,033 retained outside originals, including 776 PDF extractions. `rg --files --no-ignore` inventories the corpus; the truncated root tree and old 719 catalogue are not used as a complete domain. Three retained case-insensitive line searches scan all representatives in canonical string path order: geometry (1,154 hits), energy methods (639 hits), and finite obstruction (17 hits). Full path/line/text multisets are replayed. Broad terms such as Fano and scaling produce many unrelated hits; these counts do not certify conceptual exhaustiveness. Macros and line breaks can evade the expressions.

The complete actual A operations are the dominant antecedent. They already provide the template, pointwise displacement bound, action-independent TV tests, inductive means, path and decoration estimates, common-center propagation, exceptional incidence, and the exact final contradiction. Original F89 adds the classical proximal interface. I91 retains that interface and adds explicit fixed-scale reverse-median, exceptional collinearity and C/D midpoint estimates, then replaces the last rigidity/splitting passage by an actually generated rational certificate with a paid perturbation budget. None of the random-table combinatorics or original fixed-point iteration is a new I91 mechanism.

The relevant pinned Artin companion `An-Artin-group-with-no-geometric-CAT-0-action-September-23-2026` has an explicit 116-generator object, but its `lem:semisimple`, `lem:centralizer-character`, `lem:sector-maps`, and `lem:geometric-centralizer` use geometric-action hypotheses, stable-length limits and action-dependent orbit constants. Complete lengths, sectors and assembly operations were read, alongside its introduction. They do not supply numerical Q89 tolerances for arbitrary complete actions. The Artin proof is not audited for truth, nor is this a claim to have independently reviewed its entire diagram/localization proof.

`Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026`, `thm:main`, assumes properness for its current-filling theorem. Its complete `lem:opposite-average`/variance operation was read: it obtains an averaged lower bound from barycentric convexity, already a classical mechanism. It does not directly constrain the finite Fano midpoint configuration. `Generalized-Cartan-Hadamard-isoperimetry-and-Euclidean-equality-rigidity-September-23-2026`, `thm:equality`, concerns bounded finite-perimeter equality regions in smooth finite-dimensional Cartan–Hadamard manifolds; its exact statement is not a quantitative arbitrary-CAT(0) flat-triangle estimate. These are scoped applicability comparisons, not full readings of unrelated companion implementations.

The external primary comparisons are likewise concrete. Gromov, *Random walk in random groups*, §§3.8.B–D, treats scaling limits, almost fixed points and energy contraction for scaling-limit-stable classes including CAT(0). Kondo's retained 2006 preprint, Theorem 6.3 and Lemma 6.4 (complete proof read), supplies marked-group openness and displacement halving in complete spaces. They explain why F89's qualitative strengthening is technical; neither prints the present template's finite parameters. Izeki–Kondo–Nayatani arXiv:1210.5829v1, Proposition 2.1 and Theorem 2.9, gives gradient-gap/n-step-energy fixed-point criteria, with additional hypotheses for its random-group applications. Berg–Nikolaev arXiv:1512.01736v1, Introduction, explicitly recalls the metric Cauchy–Schwarz inequality used here. Only that K=0 statement is used; the diameter-restricted positive-curvature theorem is not imported.

Primary URLs: [Gromov](https://www.ihes.fr/~gromov/wp-content/uploads/2018/08/6106.pdf), [Kondo](https://www.math.kyoto-u.ac.jp/preprint/2006/17kondo.pdf), [IKN v1](https://arxiv.org/abs/1210.5829v1), [Berg–Nikolaev v1](https://arxiv.org/abs/1512.01736v1). The first three retained response bodies/versions are reused from sealed I89; the last PDF and version page were fetched and retained with URL, response headers, timestamp, byte count and hashes. The Springer 2008 PDF URL led to a subscription landing page, so no claim to have read that inaccessible full text is made; the authors' later primary preprint states the exact zero-curvature formula. No third-party summary supplies a geometric premise.

This bounded comparison does **not** establish worldwide novelty, a MathDB significance score, or a substantial-contribution PASS. Explicitness alone may be technical proof extraction from accepted lower operations. The author result and its finite certificate are offered for independent review without increasing the substantial count or declaring all companion operations exhaustively cleared.

## 7. Finite-presentation interface and what has not been output

For the specified T set

```
alpha=delta_sampling=1/(392T),     beta=8/(392T),
kappa=min(beta-7alpha,alpha/5,delta_sampling)=1/(1960T),
eta_separator=kappa/4,
K_fragment=(2116800 T)^2.
```

Then beta>7alpha, all required parameters lie in (0,1), and `T(beta+90delta_sampling)=1/4<1/2`. Since A's separator constant `2sqrt(2)/(1-sqrt(2/3))<18`, this K_fragment meets its D=15 separator budget. A's actual finite condition is the coincidence-rank inequality `diagram:rank-bound` for **every collection of at most 8K_fragment distinct occurrences containing all fan slots of its tops**. Its deterministic lower proof gives asphericity and a letter filling constant at most `60/kappa=117600T` when that finite condition passes. This is the actual condition, not a test of arbitrarily many diagram words.

A finite enumeration interface is now completely specified: choose even alphabet sizes `N=(2m)^(392T)`, enumerate finite subsets of every required table, and check the finite rank condition, nonempty master matches, single-field marginals, and the rational uniform-star couplings for all admissible tests through T. One can compute the maximal closure U by checking the finite subsets of the 212 fields, enumerate present injective stars, and check their exact branch and leaf TV distances; these are A's actual couplings. The six-letter comparison target `N^(1-delta_sampling)=(2m)^(392T-1)` is an integer, so its relative inequalities are rational checks as well. A's accepted sampling/rank lower operations give existence of successful realizations along this subsequence, with fixed positive parameters. Thus enumeration eventually reaches one. A finite presentation can then be read by fixed spanning-tree cycle bases and all decoration relators.

**This enumeration has not been executed to a successful table, and no literal output presentation is delivered.** The finite contraction theorem Q91 and its geometric certificate are the completed result. The extra construction/output request remains unperformed; a positive-probability argument or a specified terminating enumeration is not described as an already output presentation. There is no alphabet-size or running-time bound, no effective simplicial triangulation size claimed, and no claim of a numerical threshold for an arbitrary preselected I89 diagonal sequence. The constants apply to table instances that pass the stated finite tests.

## 8. Verification and handoff

From the research root:

```
python -B frontier/experiments/i91_finite_cat0_obstruction/checks.py
python -B frontier/experiments/i91_finite_cat0_obstruction/verify.py
```

The exact certificate checker and finite diagnostics pass. The verifier is offline and READ-ONLY: it binds the exact owned domain, original inputs and immutable references, frozen ledgers, complete-domain search multisets, passage bytes, retained primary responses and PDF extractions, the corrected rational certificate, and the original I89 evidence replay. It does not fetch, write, repair, or reseal. Canonical ordering is by full POSIX path strings throughout. Only the seal and its separate SHA-256 anchor are excluded from their own manifest. The original I89 replay still reports its historical mathematical verdict as not independently reviewed; this report's separate analytic verdict is not written into that old output.

The seal is an integrity record, not independent approval of Q91 or its contribution. In particular, exact rational trace checking supports the finite algebraic implication; independent review must still assess the geometric interpretation of every initial constraint and the error reductions, especially the missing pair Y_D--CD, the reverse-median lemma, and the perturbation accounting. Pre-seal failures and corrections are preserved. The original audit passes without repairs; the new finite contraction proof is author-level; the actual-presentation output and substantial-contribution gates remain unpaid. No old report, seal, source, finalized wrapper, shared ledger or Git index was modified.
