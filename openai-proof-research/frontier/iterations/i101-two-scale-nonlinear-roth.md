# I101 — Original arithmetic-partial audit and two-scale nonlinear Roth bridges

**Disposition: C99 remains unproved and unrefuted; no substantial nomination.** The ORIGINAL I99 claims A1–A5, the normal-character obstruction, B1–B4 and the stated local/height/support counterexamples receive **ORIGINAL PASS WITHOUT REPAIRS**, at their actual stated scopes. None is promoted to a ninth finding. New author-level results below give (i) an actual parabolic matching-matrix comparison and a block-conditioned probabilistic construction, with quantitative counts, and (ii) a shorter-window scalar graph bound, a weighted block-count criterion, and a quantitative energy alternative. The missing deterministic geometric regularization is specified in (U). Neither a general Weyl estimate nor an uncharged smoothing step is used to assert C99.

Work is confined to the three I101-owned paths. No children, shared edits, staging, commits, push, or changes to sealed originals. All theorems **and lower operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Their contracts are checked where used; their truth is not audited. I98/I100 artifacts are not dependencies. Q90/Q91 remain closed. The accepted count is eight, with two remaining; parent integration and fresh independent review are separate.

## 1. Frozen scope, evidence and exact target

The full I101 prompt, including the full I99 original brief/report/final parent evidence record, is frozen as `original-full-brief.txt`, extracted without abbreviation from the parent-owned iteration101 task record. The original iteration99 task record, report, parent verification, AGENTS, and current four ledgers have separate snapshots. I99's sealed source and experiment inventory is referenced by hash, not recursively copied. Only `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift; their snapshots may not.

The complete `sources/preprints-tree.json` has 13,223 entries, 749 manuscript directories, and 10,373 original blob positions. Reused I99/I88 mapping covers all 9,340 ignored I14 originals plus 1,033 outside originals, including 776 inherited PDF text representations. `sources/tree.json` is not used as the domain. The final replay reruns the six inherited exact lexical occurrence multisets and the additional I101 searches. This is **full-domain lexical coverage, not full semantic reading**. It replays the four selected I99 PDF extractions; it is **not all-PDF re-extraction**. All mathematical claims here have prose proofs; finite checks and file hashes are not substitutes.

`passages.json` records source file and excerpt SHA-256, exact source/proof-end ranges, immutable URLs where available, and line conventions. TeX and the report use LF splitting with terminal empty element removed. Existing Peluse–Prendiville PDF-text locators use `splitlines()` (which splits form feeds); HTML-derived text ranges also explicitly say which convention is used. The final verifier checks the convention, not merely a line number. Current arXiv version-page responses and the added multidimensional companion are retained with retrieval URLs/status/hashes. Initial truncated tool output and the rejected optional transcript query are retained in `work-log.json`; neither is called a successful full read.

**C99.** There should exist absolute constants C,B >= 2 such that, for every integer q >= 1, real 0 < delta <= 1, and integer N >= 2 satisfying

    log N >= C (log(2q) + log(2/delta))^B,

 every A subset [N] with |A| >= delta N contains

    x, x+t, x+q t^2,       integer t >= 2.

The base and integer parameter are shared. The coefficient q varies in the threshold. The work below does not replace this by prime arguments, a fixed-q substitution, or independent arguments on two edges.

## 2. Independent ORIGINAL audit

The source premises actually used positively are the fixed polynomial `h(t)=t^2` case of IP `thm:main` and elementary finite graph/linear-algebra/probability facts proved below. Source AP/IP lower operations are read as attempted-route contracts; they are not invoked on an input that fails their support or conditioning hypotheses. PP/SF/OI are relevant only to the original screening and counterexamples, not premises of a new theorem.

### A1 joint major-arc formula — ORIGINAL PASS WITHOUT REPAIRS

Let M,q,D,r be positive integers; w is any complex D-periodic weight; alpha=a/r+sigma, beta=b/r+tau, a,b integers; L=lcm(D,r). The original estimate is valid even when L>M and even when w is not positive. With c(t)=w(t)e((at+bqt^2)/r), its mean G over a period satisfies |G|<=||w||infinity. For v>=0, write v=kL+s, 0<=s<L. The discrepancy of the integer sum up to v and Gv is bounded by (floor(s)+s)||w||infinity <=2L||w||infinity. At v=0 it is zero. Partial summation against F(u)=e(sigma u+tau q u^2) has endpoint bound 2L||w||infinity and derivative integral at most 2pi(|sigma|M+|tau|qM^2). Division by M gives exactly A1. No coefficient-uniformity is being extracted from a source constant: this calculation is uniform in q by inspection.

### A2 odd-modulus local factor — ORIGINAL PASS WITHOUT REPAIRS

For odd r, g=gcd(bq,r), translation by r/g multiplies the linear phase by e(a/g) and leaves the quadratic phase unchanged modulo integers: both cross and constant changes are integers since bq/g and r/g are integers. Thus g not dividing a gives zero. If g divides a, reduction to r'=r/g is exact, with r'=1 handled separately. For r'>1 the reduced quadratic coefficient is a unit; squaring the sum and summing first in the old variable kills every nonzero displacement because 2 is also a unit. The normalized square is 1/r'. Hence magnitude sqrt(g/r), including the g=r endpoint. No even-modulus formula is asserted.

### A3 weighted Weyl and actual range — ORIGINAL PASS WITHOUT REPAIRS

The variable approximated is theta=2q beta, not beta. The hypotheses are a reduced c/r, 1<=r<=M^2, and |theta-c/r|<=r^-2. Differencing an unweighted length-M sum gives

    |T|^2 <= M+2 sum_(1<=h<M) min(M,(2||theta h||)^-1).

For r>=2, a block of at most floor(r/2) consecutive h has pairwise circular separation at least 1/(2r). Indeed a nonzero difference d<r/2 has ||cd/r||>=1/r, while the perturbation is <=d/r^2<1/(2r). Ordering distances from zero therefore bounds a block by an absolute multiple of M+r log(2r). There are at most an absolute multiple of M/r+1 blocks, including r=2,3 where the block has one entry. Expansion after division by M^2 gives terms 1/r, log(2r)/M, 1/M and r log(2r)/M^2; since r<=M^2, these fit the displayed original log(2M) bound. For r=1 or M=1 the trivial bound handles the endpoint. Expanding w in normalized D-Fourier modes changes only alpha and costs exactly sum |w_hat(j)|. Thus A3 holds with an absolute constant.

For 0<eta<=1, M^eta<=r<=M^(2-eta) gives the original M^(-eta/2) saving times sqrt(log(2M)) A_w. This controls only that specified range of the quadratic denominator. Frequencies with small quadratic denominator and varying linear frequency, the transition ranges, and a global two-variable trilinear assembly are not supplied. If A_w grows the bound may also be trivial. These are original limitations, not repairs.

### Primitive normal character — ORIGINAL PASS WITHOUT REPAIRS

For odd p not dividing q, t=r+ps modulo p^2 has p distinct lifts. The coset of two coordinates has p^2 points. The coefficient vector (-2qr,1) is primitive modulo p^2 even if r=0, because its second coordinate is a unit. On the lifts,

    -2qr t+q t^2 = -q r^2+q p^2 s^2.

Its character is constant of modulus one. This directly obstructs uniformity on the full vector coset; it does not object to the stipulated scalar kernel, whose higher-lift cancellation has a different domain. The new constructions retain the actual curve.

### A4 sharp conditional prediction — ORIGINAL PASS WITHOUT REPAIRS

Z need not itself be uniform for the inequality. Character orthogonality, conditioning on the complete Y, and Cauchy–Schwarz bound each nonzero contribution by rho/p. Summation gives 1/p+(1-1/p)rho for all 0<=rho<=1. In the original mixture, independent uniform X,T make Y=(X,X+T); the deterministic component is Z=X+qT^2, and the other component is independent uniform Z. Every coordinate is uniform, each nonzero conditional character has constant magnitude rho, and the event has exactly the displayed probability. This proves sharpness for the specified Z even at rho=0,1. It does **not** assert unchanged mixing for every coordinate of this example. In a larger tuple Y includes the two determining coordinates, so the same obstruction applies. The claimed lower bound on exceptional mass follows literally.

### A5 trilinear loss, complex and real cases — ORIGINAL PASS WITHOUT REPAIRS

With normalized Fourier transform and averages, Fourier expansion has no hidden powers of p. For each b, sum_a |f0_hat(-a-b) f1_hat(a)| <= ||f0||2 ||f1||2; then sum_b |f2_hat(b)| <=sqrt(p)||f2||2. The exact inequality follows for arbitrary complex K and L2 inputs, hence for the stated bounded inputs.

For the chirp example, v=-u makes the combined quadratic exponent

    2c u^2+2c x^2-c(x+u)^2-c(x-u)^2=0.

The factor p times the line indicator cancels its probability 1/p. Every multiplier has magnitude p^-1/2 by A2, since 2c is a unit for odd p. For Re K the same complex test has value (1+E_u e_p(-4cu^2))/2. Its modulus is at least (1-p^-1/2)/2, and ||(Re K)_hat||infinity<=p^-1/2. The original **real assertion concerns the kernel**; its tests remain complex, exactly as written. If real inputs are desired as well, expanding each chirp into real and imaginary parts gives eight real 1-bounded product tests. At least one has absolute pairing >=(1-p^-1/2)/16. Their L2 norms are at most one, proving the same order obstruction with real inputs. This last observation is an extension, not a required repair. None of these kernels is claimed to be the parabolic kernel.

### B1 covariance — ORIGINAL PASS WITHOUT REPAIRS

For integer a and positive d,q, the image of (x,x+t,x+(qd)t^2) under y->a+dy is (a+dx,a+dx+dt,a+dx+q(dt)^2). The coefficient after restriction is qd. A count with restricted t>=2 is a valid original count with parameter dt>=2. For d>=2, t=1 can sometimes be retained; the original deletion is conservative, never invalid.

### B2/B3 counting and every endpoint — ORIGINAL PASS WITHOUT REPAIRS

IP `thm:main` has degree-only exponent and polynomial-dependent C_h,N_h. Apply it only to the fixed h=t^2. Replace its exponent by a smaller positive c if desired and enlarge C to cover the finitely many lengths below N_h: for example C>=max(C_h,N_h^c,1) suffices. This supplies alpha_square(L)<=C L^(1-c) for **every integer L>=1**, with C,c independent of q,D. It is not an illicit uniform statement for all polynomials.

For Q=qD^2 and M=floor(sqrt((N-1)/Q))>=1, a residue class modulo Q has at most L=ceil(N/Q) vertices. All square differences that fit that class have t<=M. An independent subset is therefore square-difference-free after reindexing, even in the shorter end classes. There are at most Q nonempty classes; consequently B=min(N,QC L^(1-c)) is a valid real upper bound on independence and is positive. Multiple parameters cannot give the same simple edge because t is positive.

For a>0, random ordering yields the independent-set lower bound sum_v 1/(deg(v)+1)>=a^2/(2E+a). Applying the ambient bound B gives 2E>=a^2/B-a. For a=0 the final inequality is zero versus zero and is checked directly, so no division by zero occurs.

For finite A, sum_x 1_A(x)(1-1_A(x+s)) is half its translation L1 distance for every integer s. Ends and beginnings on each finite D-chain agree, including the zero-extension boundaries. The triangle inequality gives D_A(Dt)<=t V_D(A). At fixed t, every edge with a missing middle point is among these directed losses; no disjointness across t is required because pairs (x,t) are counted. Summing costs V_D M(M+1)/2. Removing t=1 costs at most a. This gives exactly 2T>=a^2/B-3a-V_D M(M+1), even for M=1, where T=0. B3 follows for a C99-avoiding A because every retained parameter Dt is at least two. A negative right side gives no information; the maximum with zero is valid.

### B4 recurrence and literature scope — ORIGINAL PASS WITHOUT REPAIRS

For j=0,1,... the first inequality follows by induction. Substituting r_i<=2^i(r_0+E), summing the geometric convolution, and bounding sum_(i<j)2^(-(j-1-i))<=2 proves the original lower bound on ell_j, with the stated K,E>=0. At j=0 it is simply the weaker ell_0>=ell_0-2E. The factor (2^(j+1)-2^(1-j))/3 is exact. The conclusion concerns the recurrence's available guarantee, not an upper bound on all possible algorithms.

Peluse–Prendiville v2 Lemma 2.1 and its proof retain N^(1/2) and stride qq', so B1 makes the next coefficient q^2q'. Shao–Wang v2 Theorem 2.4 already allows a shorter M, and Lemma 4.1 already has separate resolutions M^(deg P_i). Lemma 4.2 and its terminal iteration still retain the exponent deg(P1)/deg(P2)=1/2 and coefficient q_next=q^(b+1)q'. Thus improving just a polynomial cost term does not remove the geometric length/coefficient factors. These literature rules forbid their specified nontrivial parameters; they cannot be literally applied just from avoidance of positive t>=2 without handling signs and t=1. I99 uses them as a comparison, not as a completed application to C99, so this distinction does not require repairing B4.

### Local/height/support counterexamples — ORIGINAL PASS WITHOUT REPAIRS

* For h_H(t)=H(t-1)^k, t=1 is a unit root modulo every modulus. For primes p>=2 every nonzero h_H(p)>=H. If N<H then [N]-[N] contains no such value. To defeat a proposed universal C,c,N0 choose N>=N0 with C N^(1-c)<N and then H>N. This does not refute coefficient-dependent thresholds.
* Modulo two, t^2 and (t-1)^2 have opposite parity; an even base cannot have both shifts even. Their individual intersectivity is insufficient.
* For t^4+4 and (t-1)^4+4, one value is 0 mod 4 for every t. Each polynomial separately has an odd input for which its value is odd; at input 0 or 1 its value is 4, excluding any odd fixed prime-square divisor. Derivative 4t^3 (respectively 4(t-1)^3) has no common root with the polynomial. Thus separability and separate squarefree admissibility hold while joint admissibility fails.
* For A=d[H], d>H>=3, any pair x,x+t in A has d|t. A square endpoint would require t^2<=d(H-1)<d^2, impossible for positive nonzero t divisible by d. The H-term linear AP in A is explicit. This invalidates a support implication, not C99's threshold.

**Audit categories kept separate.** ORIGINAL PASS WITHOUT REPAIRS: every item above. PASS AFTER REPAIRS: none. FAIL at stated original scope: none. Stronger extrapolations (global A3 assembly, simultaneous unchanged A4 mixing, dimension-free arbitrary A5 transfer, automatic low variation, or nonlinear-free implies AP-free) fail or remain unproved as explicitly indicated; they are not silently substituted for the originals. Contribution verdict: technical partials only.

## 3. Common paid tool: freely chosen local windows

Fix absolute C>=1 and 0<c<=1/4 so that alpha_square(L)<=C L^(1-c) for all integer L>=1, as above. Write K=4C. Let N,q,D be positive integers, M>=2 an integer chosen freely, Q=qD^2, W=QM^2+1, R=ceil(N/W), and

    B_M = min(N, R Q C (M^2+1)^(1-c)).                 (1)

Let G_M have vertex set [N] and edges {x,x+Qt^2} for 1<=t<=M with both endpoints in [N]. Then

    alpha(G_M)<=B_M;
    if N>=W,  B_M<=K N M^(-2c).                      (2)

**Proof.** Partition [N] into R consecutive windows of length W, with the last possibly shorter. Within any one window, every square difference in any fixed Q-residue class has parameter at most M because its distance is at most W-1=QM^2. Reindexing gives a square-free independent subset of an interval of length at most M^2+1. Sum its bound over at most Q classes and then R windows. Edges crossing windows are discarded only in this upper bound on independence; discarding them cannot invalidate the conclusion. If N>=W, R<=2N/W and (M^2+1)^(1-c)<=2 M^(2-2c), proving the second bound. The final incomplete window and all residue endpoints are paid. ∎

For a=|A| and zero extension, exactly the original graph proof now gives

    2 T_(D,M)(A) >= a^2/B_M -3a -V_D(A)M(M+1),       (3)

where T counts x,x+Dt,x+Qt^2 with 2<=t<=M. This is an actual local-window graph bound, not applying the scalar theorem to an incomplete polynomial value set on the entire interval.

For example, if a=delta N, N>=W,

    M^(2c)>=12K/delta,
    V_D(A)/a <= delta M^(2c)/(4K M(M+1)),

then T>=delta^2 N M^(2c)/(4K). Indeed the -3a and variation terms each consume at most one quarter of the main lower bound in 2T. Taking M of order delta^(-1/(2c)) makes the sufficient stability polynomial in delta and independent of N (constants can be very large). This improves I99's **budget**, not the density theorem: the stability premise is still a real restriction.

A weighted graph fact will be useful. For every nonnegative vector h on a graph of independence number at most B,

    sum_v h(v)^2+2 sum_{uv edge} h(u)h(v)
       >= (sum_v h(v))^2/B.                          (4)

To prove it, minimize the left side at fixed total mass. If two adjacent vertices carry mass, move their combined mass to one of the two: their own contribution is unchanged and all other contributions are affine in the moved mass. One endpoint choice does not increase the objective. Repetition leaves independent support, of size at most B, where Cauchy–Schwarz proves (4). Compactness or this finite elimination works also when B is a real upper bound. Zero total mass is immediate.

## 4. Route I: the actual parabolic matrix and a two-scale construction

### 4.1 A middle-slot comparison which retains the curve

For real r:[N]->[-1,1], extended by zero, form the N by N matrix

    A_r(x,z) = r(x+Dt) if z=x+Qt^2 for an integer 2<=t<=M,
               0 otherwise.                         (5)

The middle point lies between endpoints: Dt<=Qt^2 for all t>=1. Each (x,z) has at most one positive parameter. For arbitrary complex 1-bounded endpoint functions u,v,

    |sum_(x,t valid) u(x) r(x+Dt) v(x+Qt^2)|
       <= N ||A_r||op.                              (6)

This follows from the ordinary Euclidean operator norm and ||u||2,||v||2<=sqrt(N). In particular, if f=1_A and 0<=g<=1,

    |T(f,f,f)-T(f,g,f)|<=N||A_(f-g)||op.              (7)

Here T is the unnormalized sum over 2<=t<=M with all vertices in [N]. This is a comparison for the **actual** kernel, not Fourier sup-norm transfer for arbitrary kernels. The normalized middle cut seminorm

    cut_(D,M)(r)=sup_|u|,|v|<=1 |T(u,r,v)|/(NM)

is bounded by ||A_r||op/M. Its definition can be tested without referring to the unknown triple count, since it ranges over all two endpoint functions.

Group the matrix entries by the middle point y:

    A_r=sum_y r(y) B_y,
    B_y has entries (y-Dt, y-Dt+Qt^2), 2<=t<=M.      (8)

For fixed y these entries have distinct rows and distinct columns. Rows are strictly decreasing in t; the column increment is Q(2t+1)-D>0. Thus B_y is a partial permutation matrix. Its Hermitian dilation H_y on 2N vertices is a matching. The union of the H_y has maximum degree at most M-1, since a fixed endpoint and parameter determine the other endpoint and the color y. This also works if the residual is in the first or last slot: grouping by that fixed vertex leaves a matching between the other two vertices. For the last slot the remaining middle coordinate z-Qt^2+Dt is strictly decreasing. These facts are specific geometric input, with no ambient-prime square-root loss.

Modulo p^2 the matrix still samples (t,qt^2), so the character in §2 remains constant on its prescribed residue fiber. We have not replaced the curve by a full coset, and have not asserted conditional mixing of a vertex against its two determining companions.

### 4.2 Quantitative random comparison, proved by colored walks

Let xi_y be independent real mean-zero random variables with |xi_y|<=1. For any integer k>=1 and any s>0,

    Pr{||A_xi||op >= s}
       <= 2N (2k)^(2k) (M-1)^k / s^(2k).            (9)

**Proof.** Dilate A_xi to S=sum_y xi_y H_y. Expand E tr(S^(2k)) as closed colored walks. A color occurring exactly once has zero expectation by independence. Every surviving walk has at most k distinct colors, and each absolute expected monomial is at most one. There are 2N starting vertices. A pattern of identifications of the 2k color positions has at most (2k)^(2k) possibilities. At a first occurrence of a color there are at most M-1 incident edges to choose; at a repeated occurrence its matching gives at most one continuation. Hence there are at most 2N(2k)^(2k)(M-1)^k surviving walks. Since S is real symmetric, ||S||op^(2k)<=tr(S^(2k)); ||S||op=||A_xi||op. Markov proves (9). ∎

For 0<zeta<1, taking k=ceil(log(2N/zeta)) gives ||A_xi||op<=4k sqrt(M) except with probability zeta. For all three slot matrices simultaneously take k=ceil(log(6N/zeta)) and use a union bound. Thus for independent Bernoulli variables f(y) of means mu(y), **arbitrary prescribed** 0<=mu<=1,

    |T(f,f,f)-T(mu,mu,mu)|<=12N k sqrt(M)            (10)

with probability at least 1-zeta. The telescoping identity uses residual xi=f-mu once in each of three terms; the other factors may depend on xi, since (6) is uniform over them. No false conditional independence of those factors is used.

For instance, if mu(y)>=beta>0 for every y, QM^2<=N/2, and sqrt(M)>=96 k beta^-3, then (10) proves

    T(f,f,f)>= beta^3 N(M-1)/4.                     (11)

Indeed the number of allowable pairs is sum_(t=2)^M(N-Qt^2)>=(M-1)N/2; the displayed size condition makes the error at most beta^3 N(M-1)/4. This is a genuine count under an explicit random law, not a claim about every set of comparable density.

### 4.3 Block conditioning and the sharper count when the profile can vanish

Partition every D-chain in [N] into blocks of lengths between H and 2H-1, possible if N>=DH. Let mu be any prescribed [0,1]-valued function constant on these blocks with mean delta. Extend it by zero. Its half-L1 D-variation satisfies

    V_D(mu) = (1/2)sum_Z |mu(x+D)-mu(x)|
             <= sum_blocks value(mu) <= delta N/H. (12)

Every block contributes at most twice its value to total jump variation, including exterior zeros. Also sum mu^2>=delta^2N. Apply (4) with h=mu^2 to G_M, and compare the middle value mu(x+Dt) to mu(x) using the positive translation loss. Since mu(z)>=mu(z)^2,

    2T(mu,mu,mu)
      >= (sum mu^2)^2/B_M -sum mu^4
          -2 sum mu -V_D(mu)M(M+1).                 (13)

The t=1 deletion costs at most sum mu, and positive translation loss at step Dt is at most t V_D(mu); all other factors are at most one. In particular if N>=max(W,DH) and

    M^(2c)>=12K delta^-3,
    H>=4K delta^-3 M(M+1)/M^(2c),                   (14)

then

    T(mu,mu,mu)>= delta^4 N M^(2c)/(4K).             (15)

This is a two-scale profile: the middle-shift scale is DM; the block length is DH; the square-graph window is QM^2. The proof does not require the square endpoint to stay in the same block or even the same window. It uses actual graph edges, with the window partition only bounding independence.

For the independent Bernoulli construction with these means, expectation of the actual triple count is exactly T(mu,mu,mu): t>=2 makes all three vertices distinct, including q=D=1. Changing one Bernoulli variable changes at most 3(M-1) triples. The bounded-difference martingale inequality therefore gives

    Pr{T(f,f,f)<T(mu,mu,mu)/2}
       <= exp(-T(mu,mu,mu)^2/(18N(M-1)^2)).          (16)

For completeness, revealing independent variables one at a time gives martingale differences whose conditional ranges have length at most 3(M-1). The elementary convex-exponential bound for a centered variable of range length b is E exp(lambda X)<=exp(lambda^2 b^2/8). Multiply these conditional bounds and optimize lambda to get Pr{Z-EZ<=-s}<=exp(-2s^2/sum b_i^2). This proves (16), with no distributional approximation.

Combining (15),(16), and the same scalar inequality for |A|, the block-conditioned construction satisfies

    T(A)>=delta^4 N M^(2c)/(8K),   |A|>=delta N/2,    (17)

except on a set of probability at most

    exp(-delta^8 N M^(4c-2)/(288K^2))
       +exp(-delta^2 N/2).                          (18)

This construction permits zero blocks and arbitrary block densities, with all q,D dependence paid in N>=qD^2M^2+1 and N>=DH. No actual subset is replaced by its average in (17): A is the original random indicator and (16) controls its count.

If desired, the **observed** block average g=E(f|blocks) also has a matrix comparison. For J blocks, a union bound on their Bernoulli averages gives

    ||A_(f-g)||op/M
      <=4 ceil(log(4N/zeta))/sqrt(M)
        +sqrt(log(4J/zeta)/(2H))                    (19)

with probability at least 1-zeta. Apply (9) to f-mu, bound each block average deviation from mu by the second term, and use the row/column degree bound ||A_r||op<=M||r||infinity for the correction. This pays the dependence introduced by conditioning; it does not call the centered block residual independent.

**A retained failed combination.** The scalar lower count in (15), divided by NM, has size delta^4 M^(2c-1). The general random matrix bound is of size log(N)/sqrt(M). With our admissible c<=1/4, increasing M does not make that *upper error bound* smaller than the scalar lower count. We therefore cannot deduce (17) merely by combining (10) and (15). The separate concentration argument (16) is essential for this random construction. This is a failure of those numerical estimates, not a lower bound proving that the actual cut norm is large, and not a refutation of C99.

## 5. Route II: deterministic density/stability and the precise missing regularizer

### 5.1 A density-preserving weighted count, with its comparison cost exposed

Let f=1_A, a=delta N, and let g=E(f|the D-chain blocks of §4.3). Thus sum g=a, 0<=g<=1, sum f g=sum g^2>=delta^2N, and V_D(g)<=a/H. The average g is a **weight**, not a subset of A.

Set h=f g and S=sum h. For each positive square edge x,z, f(x)g(x)f(z)>=h(x)h(z). Using (4), the same positive-loss calculation, the t=1 deletion, and (7), gives the exact deterministic inequality

    2T(A)>= S^2/B_M -sum h^2 -2a
                  -V_D(g)M(M+1)-2N||A_(f-g)||op.   (20)

One may replace the last term by -2NM cut_(D,M)(f-g). This is preferable if a cut comparison is available but a spectral comparison is too expensive. All endpoints in (20) still belong to A; the middle point is returned to f by the displayed error. Since sum h^2<=a,

    2T(A)>=delta^4 N^2/B_M-3a
                  -(a/H)M(M+1)-2NM cut_(D,M)(f-g). (21)

Consequently, (14), N>=max(W,DH), and

    cut_(D,M)(f-g)<=delta^4 M^(2c-1)/(8K)            (22)

imply T(A)>=delta^4 N M^(2c)/(8K). Each of the three deducted errors in (21) consumes at most one quarter of delta^4NM^(2c)/K. There is no uncharged factor of D or q: D controls chain membership, Q controls graph windows, and the same t drives both shifts.

### 5.2 Why low-variation subset selection is not automatic

For any finite A, D>=1 and integer L>=2, let U_(D,L)(A) be the vertices lying in at least one fully occupied D-run of length L. Every B subset A satisfies the deterministic inequality

    |B| <= (L-1)V_D(B)+|U_(D,L)(A)|.                (23)

Decompose B into maximal D-runs. Each short run contributes at most L-1 vertices and one beginning. Every vertex of a long run lies in a length-L subrun and hence in U. This proves (23), including truncated end runs.

For an independent Bernoulli-theta A, each vertex belongs to at most L possible length-L runs, so E|U_(D,L)|<=NL theta^L. Markov gives, for fixed D and 0<zeta<1,

    |U_(D,L)|<=NL theta^L/zeta

with probability at least 1-zeta. Thus if |B|>=kappa N and L theta^L<=kappa zeta/2, **every** B subset A of that size has V_D(B)>=kappa N/(2(L-1)). With a predetermined finite list of s strides replace zeta by zeta/s. This is a density-retaining obstruction, stronger than observing that V_D(A) itself is usually large. It does not forbid choosing an unrestricted, data-dependent stride; its domain is explicitly fixed. It also does not rule out a weighted or pseudorandom branch.

The periodic test A={n in [N]:n mod 5 in {0,1}} has no D-run of length three for any D not divisible by 5. Hence every B subset A satisfies V_D(B)>=|B|/2 for such D. For 5|D, by contrast, V_D(A)<=D. Selecting D=5 solves that elementary variation obstruction but replaces Q=q by 25q in the graph and the coefficient by 5q on an AP restriction. Such periodic sets contain actual parabolic triples at sufficiently large N; this is no C99 counterexample.

Smoothing really can create triples: in [5], A={1,2,3,4} has no positive-parameter t>=2 triple for q=1, while its one-block average 4/5 has count (4/5)^3 from (1,3,5). The discrepancy term in (20) cannot be discarded. This finite example is far outside the C99 threshold and refutes only that selection shortcut.

### 5.3 A paid energy alternative, and what it does not preserve

For fixed q,D,M and any partition P of [N], put g=E(f|P). If cut_(D,M)(f-g)>epsilon, endpoint witnesses u,v define

    psi(y)=M^-1 sum_(2<=t<=M, endpoints valid)
                   u(y-Dt)v(y-Dt+Qt^2),

with |psi|<=1 and |E_y(f-g)psi|>epsilon. Rotate the phase and take its real part to get a real [-1,1]-valued psi with positive correlation >epsilon. Quantize its values in intervals of width epsilon/4 and refine P by this partition, using at most ceil(8/epsilon)+1 new parts per old atom. Let g'=E(f|P'). The quantized psi is P'-measurable, so orthogonality and |f-g|<=1 give

    ||g'-g||_(L2([N])) >=3epsilon/4,
    ||g'||2^2-||g||2^2>=9epsilon^2/16.              (24)

Indeed the quantization changes the correlation by at most epsilon/4; pairing g'-g with the quantized function, whose magnitude is at most one, proves the first estimate. The second is the projection identity. Iterating stops within ceil(16/(9epsilon^2)) strict refinements with cut discrepancy at most epsilon, and multiplies atom count by at most

    (ceil(8/epsilon)+1)^ceil(16/(9epsilon^2)).         (25)

This is an actual alternative, not a promised density increment: failure of the cut branch yields a specified energy increase. The price is that these dual-function level sets need not be arithmetic blocks, polynomial patches of controlled rank, or have small V_D. The mean is preserved, but variation is not. The energy bound alone has polynomial inverse-epsilon cost; when epsilon is a power of delta its logarithmic complexity is a power of 1/delta, not a polynomial in log(1/delta).

### 5.4 Strong lower AP operations: usable geometry, missing nonlinear contract

The accepted AP source is substantially stronger than a qualitative AP theorem. Its `ap:absolute` returns only (2+p)^C fresh slots, independently of ambient box dimension, and its relative lifting returns rank d+d0. In the full lifting proof, the base case uses injective **affine** samples and explicitly invokes inheritance of linear-progression-free support (07-lifting.tex, LF 1230–1235). The scalar score transfer itself can treat a fixed positive patch for a general bounded f with the prescribed sampler inputs. It does not create that patch or establish a nonlinear count. Old-layer removal restores at most D slots after removing D; depth is bounded by the fixed number of weights, not the number of increments. Its full proof-end recurrence is

    F_j(p)<=(2+p+F_(j-1)((2+p)^c_s))^C_s,  j<=s.

Those lower operations are accepted in full; no alleged upstream gap is used. But they do not license feeding an arbitrary dual level set from (24) to `ap:absolute`. They also do not prove that a nonlinear forbidden configuration is inherited under the needed multidimensional sampling rule with fixed coefficient. Under an injective one-dimensional affine restriction stride d, the correct inherited coefficient is qd, by B1. A general spatial affine map u->a+L(u) and parameter direction v replaces it by q L(v); the coefficient depends on the chosen direction. Injectivity on a finite box does not fix L(v) or its sign. This is a second contract to pay, in addition to support and cut comparison.

Here is an explicit conditional resource calculation, not an asserted nonlinear rule. Let P=2+log(2q)+log(2/delta), T<=C0P. Suppose a *new, valid nonlinear* increment retained fixed weight depth s and satisfied, after appropriate forecasts,

    d_i(j+1)-d_i(j) <= (2+P+sum_(h>i)d_h(j))^A,
    Q_i(j+1)-Q_i(j) <= (2+P+d_*+sum_(h>i)Q_h(j))^A,
    log d_stride(j) <= P^L,
    ell_(j+1)>=ell_j-P^L,
    r_(j+1)=r_j+log d_stride(j).                    (26)

Here Q_i are width logarithms (not the coefficient qD^2); d_* includes all preparation and fresh-coordinate forecasts. At the top weight d_s<=d_s(0)+T(2+P)^A. If higher dimensions are bounded by a polynomial F_(i+1)(P), then d_i<=d_i(0)+T(2+P+sF_(i+1)(P))^A. Descending at most s times gives a polynomial dimension forecast. Repeat this explicit induction for Q_i with that forecast. For example degrees obey e_s=A+1 and e_i<=1+A max(1,e_(i+1)); the width degrees obey the same finite recursion with max including deg d_*. Each forecast has fixed degree because s is fixed. Summing stride and length costs gives r_T<=r_0+C0P^(L+1) and ell_T>=ell_0-C0P^(L+1). After enlarging L to cover all forecasts, a polynomial initial log N budget would suffice. No width can be substituted into its own loss recurrence; such substitution would change this calculation.

Thus the AP lower operations show exactly what would be useful **if** a nonlinear certificate with these hypotheses existed. The present dual-function refinement does not supply its rank, width, sampler, or coefficient guarantees. Existing PP/SW progressions instead have a square-root length cost, and q grows at least in the supplied recurrence as a fixed power at each step. For r_next<=lambda r+E and ell_next>=ell/2-Kr-E, the resource convolution contains 2^j lambda^j (with the coincident-base case handled by a j factor). Even if E is polynomial in log(1/delta), j of order log(1/delta) leaves a power of 1/delta. A shorter M by itself changes the window of the inverse theorem, not that preservation problem. SW Theorem 2.4 already includes all M up to the natural scale; this freedom is not being claimed as new.

### 5.5 Exact unpaid inequality and threshold budget

One sufficient unresolved statement is the following **(U)**. For every A in C99's density/length range, either there is already a triple, or there exist positive integers D,H,M, M>=2, such that

    qD^2 M^2+1<=N,       DH<=N,
    M^(2c)>=12K delta^-3,
    H>=4K delta^-3 M(M+1)/M^(2c),
    cut_(D,M)(1_A-E(1_A|balanced D-chain H-blocks))
         <=delta^4 M^(2c-1)/(8K),                   (U)

with all selection and any prior restriction costs at most a fixed polynomial in P. For an AP restriction the current coefficient is q times the product of all strides; that coefficient must replace q in (U). More concretely the available ambient length must pay

    log(qD^2M^2+1),  log D+log H,

in addition to every earlier lost logarithmic length, all slot counts and all width precisions. The numerical stable-branch requirements alone allow log M, log H=O_(C,c)(log(2/delta)); they are not the hard part. The selection/comparison assertion in (U) is unproved, and (24) does not prove it because it destroys the block geometry. If D were allowed to be so large that every chain was short, the premise DH<=N would explicitly fail. There is no hidden such escape.

An alternative useful unpaid rule could return general positive patches instead of these blocks, but would then have to replace (12), prove the actual trilinear comparison, retain normal characters, and establish the finite-depth losses in (26). Merely attaching the old AP lifting theorem to the end does none of these.

## 6. Literature, contribution and validation limits

Current version pages checked in this run still identify Peluse–Prendiville [2003.04122v2](https://arxiv.org/abs/2003.04122v2), Shao–Wang [2505.16822v2](https://arxiv.org/abs/2505.16822v2), and Altman–Sawhney [2506.13010v1](https://arxiv.org/abs/2506.13010v1). Their actual relevant statements, local inverse/regularity operations and terminal proof ranges are indexed, not inferred from titles. The original integer transfer comparison in Altman–Sawhney has its displayed double-logarithmic error; replacing an AP input alone does not establish this nonlinear uniform family.

The added Peluse–Prendiville–Shao [2407.08338v1](https://arxiv.org/abs/2407.08338v1) already supplies an exponential-in-inverse-error popular-difference threshold, including the one-dimensional pattern. Theorems 1.2–1.3 and the complete §7 deduction were inspected. It is a stronger relevant popular-count companion, but its threshold still has powers of inverse density when used for existence; it does not give C99's logarithmic-height threshold. The absolute-version page and the date printed by the generated HTML differ in kind; we record version v1 from the archive, not a new version inferred from the rendering date. No primary literature theorem is used as an unproved positive step in (1)–(25).

C99 belongs to the named nonlinear Roth / polynomial Szemerédi problem; the primary introductions document that significance. No verified MathDB identifier, universal novelty claim, formal certification, or peer-review claim is supplied. The new local-window accounting is sharper than I99 B2 when a short M is freely selected. The matching decomposition and colored-walk comparison use actual common-parameter geometry, and the block-conditioned construction gives actual indicator counts with explicit probabilities. These remain technical bridges: they do not demonstrate a substantial improvement over both the stipulated corpus and primary literature for an arbitrary dense class. The random model and the low-variation deterministic class are not nominated as easy substitute findings.

The final command is:

    python3 -B frontier/experiments/i101_two_scale_nonlinear_roth/verify.py

It is offline and read-only: no downloads, output files, bytecode, repair, or reseal mode. Preparation is a separate script and is never imported. Prevalidation is run before the one final seal; the seal excludes itself and its hash is given in the handoff. Exact owned inventory, immutable references, complete inherited domain, exact lexical multisets, passage conventions, selective PDF bytes and finite diagnostics are checked. Failed quantitative combinations and finite smoothing/selection examples are retained as failures of proposals. Parent integration and a fresh independent review of any future candidate remain necessary.

The additional full-domain expressions have occurrence counts 0, 267, 62, and 803. The 27 passage records include individual original I99 proof ranges and separate primary proof-end markers. Finite I101 checks cover 120 local graph bounds, 24,552 short-cutoff indicator cases, 1,092 weighted graph and 1,092 weighted profile cases, 992 block-average cases, 3,132 matching decompositions, 45 colored-walk moments, five exact inhomogeneous Bernoulli expectations, 29,511 nested-subset run cases, 63 random-run expectations, 218 energy refinements, and 25 periodic strides. Zero lexical hits in the first expression means only zero matches for that exact expression.
