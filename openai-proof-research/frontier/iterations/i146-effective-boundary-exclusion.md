# I146 — Original I143 audit and effective boundary exclusion

2026-10-10. **Original I143 paid mathematical assertions: PASS without repairs at their stated scopes. New original FAIL: none. Unresolved original paid assertion: none.** The originally unpaid effective K0 and reflected radial pressure remain unpaid; they are not included in this PASS. The I143 parent review was selective and is not the basis for a blanket original-proof verdict.

**Disposition: PARK numerical boundary exclusion; no nomination; eight accepted findings remain eight, two remain.** This report adds finite-domain mass/remainder estimates, a Hölder-compatible interval retention rule, a cancellation-preserving reflected vector estimate, and an explicit boundary-first-moment remainder estimate. These are technical partials, not a numerical replacement for the complete annular input. No counterexample to Target L is claimed. All other parked branches remain parked.

All OpenAI theorems **and lower proof operations** at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. There is no upstream truth audit, contradiction inference or ex-falso. External papers remain ordinary evidence. No children, shared edits, staging, commits or publication; active I144/I145 outputs are not dependencies.

## 1. Original-context gate and independent original audit

The mandatory original record `iteration143-weighted-boundary-pole-control-task.json`, SHA-256 `cd007ff0fb20c881443cdd1130ed094eda4861f1a94e806637fa538f73da45a1`, was frozen and every decoded field read. The nine recursive decoded records total 5,320 splitlines, including the original briefs, reports, finalized responses and objections down through the embedded I116/I113 records. The I143 report and complete finalized parent receipt were independently frozen and read, as was the separately referenced complete I116 parent receipt. Read ranges, endings and hashes are recorded. The gate preceded this mathematical audit. Discovery listings and truncated displays are not treated as complete reads.

AGENTS.md and the pinned upstream identity were read. Current ledger snapshots were inspected for status, not claimed to have been semantically read through every historical entry. The original complete corpus map and 776 PDF/text bindings are reused by reference. Byte coverage of that corpus is not semantic proof reading.

### 1.1 Green representation, kernel and interval assertions — PASS without repairs

Use `S_n=|S^{n-1}|`, `k_n=1/((n-2)S_n)`, `R(y',y_n)=(y',-y_n)`, and `K(z)=k_n|z|^{2-n}`. The half-space kernel is `G(x,y)=K(x-y)-K(x-Ry)>0`. On an exhaustion, positive Dirichlet Green potentials increase and are bounded above by the corresponding solution. Their limit has the correct distributional Laplacian locally; the residual is nonnegative harmonic. Under I143's actual global bound it is bounded and has continuous zero plane trace, since it lies between zero and the continuous solution. Odd reflection of this **harmonic residual**, followed by bounded harmonic Liouville, eliminates it. This does not reflect a positive nonlinear solution into the stipulated whole-space class. For an unbounded function, the argument alone does not eliminate a multiple of x_n. I143 stated that limitation.

Let `r=|x-y|`, `s=|x-Ry|`, `s²=r²+4x_n y_n`. Direct integration gives

`G=k_n(n-2) int_r^s t^(1-n)dt`.

Writing `z=4x_n y_n/r²`, the factor is `1-(1+z)^(-(n-2)/2)`. On 0≤z≤1 the mean-value bounds lie between `((n-2)/2)2^(-n/2)z` and `((n-2)/2)z`; on z≥1 it lies between `1-2^(-(n-2)/2)` and 1. This proves I143's two-sided minimum estimate, including both regimes, with dimensional constants. It also proves the loss of a uniform comparison from below to K.

For a tangential unit e, put `h=e·(x-y)` and let a,b be the transverse line distances, 0≤a<b. Away from the null coincident-line singularity,

`-G'(h)/h=(n-2)k_n(n/2) int_(a²)^(b²) (h²+t)^(-(n+2)/2)dt`.

This is the actual positive even decreasing derivative kernel. Moreover

`J_e = n h² [int_(r²)^(s²) t^(-(n+2)/2)dt]/[int_(r²)^(s²) t^(-n/2)dt] <= n h²/r² <= n`.

This integral ratio tends to n when s/r→1 and h²/r²→1, achievable with positive heights tending to zero and tangential alignment. The sharp dipole limit is thus paid, not merely sampled.

For intervals I,J the push-forward of ds dt under h=s-t is the symmetric trapezoid `F(|h-d0|)` with F nonincreasing. For d0≥0, its value at h>0 is at least its value at -h. Pairing against the actual odd function `-G'(h)` gives `d0 int[-G'(h)]>=0`. Midpoint integration by parts therefore yields

`int(2G-Gbar_I-Gbar_J) <= int J_e G`.

Multiplication by min(c_I,c_J), and positivity of each endpoint average for the excess coefficient, gives the unequal-weight inequality with `|c_I-c_J|G`. If a partner interval is unbounded and its coefficient is zero, use the nonnegative extended-integral formulation; no infinite subtraction occurs. This independently verifies the claimed operation. Subtracting two Newton-kernel upper bounds would not prove it.

For `X=x eta(|x|)`, reflection equivariance gives exactly

`-(Xx·grad_x+Xy·grad_y)G = (n-2)k_n {[(Xx-Xy)·(x-y)]r^-n - [(Xx-RXy)·(x-Ry)]s^-n}`.

With eta=1 the answer is `(n-2)G`. The sharp tangential n therefore does not refute a radial theorem. Positive-level source endpoints cannot terminate at finite plane points for nonnegative weights and zero continuous boundary values. Nevertheless the non-tangential reflected line geometry changes, and normal derivatives on the plane need not vanish. I143 correctly left that pressure extension open.

### 1.2 Annular K0 and geometry — PASS without repairs, non-effective

K0 is a local estimate away from the weight pole, on an inner annulus separated from its two artificial spheres. Doubling uses the **unweighted** exponents `alpha0=2(p+1)/(pq-1)`, `beta0=2(q+1)/(pq-1)` and the joint gauge, with distance only to the artificial boundary. The zero physical boundary is retained. At the secondary scale mu, the annular weights have positive lower bounds and controlled moduli; coefficient oscillation is O(mu^theta) on each fixed ball. After recentering and rotating at a nearest physical boundary point, graph slopes relative to the tangent plane are O(mu R), Hessians O(mu). The alternative is a whole-space limit.

The doubling gauge bounds both rescaled components and normalizes their sum of powers; it does not lower-bound both center values. Boundary W^(2,r), r>n, excludes zero limiting distance of the normalized center from the physical boundary. These estimates hold on uniformly one-sided C^(1,1) graphs for the Laplacian with bounded right sides and zero trace; Hölder coefficients are used for freezing, not differentiated. C^(1,1) is sufficient for W^(2,r) and C^(1,nu) compactness on smaller patches; no C² Schauder norm uniform over all such graphs is asserted. Coupling and the strong minimum principle then give positivity of both limit components. For constants a0,b0, setting U=s u,V=t v removes them by

`log s-p log t=-log a0`, `log t-q log s=-log b0`.

The nonzero determinant 1-pq and compact positive coefficient interval give uniform finite amplitude factors. Neither component is discarded.

The stipulated entire theorem plus the separate unweighted half-space operation excludes the normalized limits. This does not invoke H143 or the desired weighted boundary-pole bound and is noncircular. PQS Proposition 7.1 expressly distinguishes the free sphere from the physical plane; Phan's Section 4 supplies the coefficient/annular mechanism but starts its bounded-domain pole argument with an interior origin. The wider stipulated entire premise changes the available exponent range, not those operations.

Weighted rescaling on annuli uses `alpha=(2+A+p(2+B))/(pq-1)` and `beta=(2+B+q(2+A))/(pq-1)`. It cancels both equation amplitude powers. At radius r≤rho the coefficient modulus is at most H r^theta and the graph curvature norm scales by r. With constant coefficients on a flat half-space the same input applies at **every radius**. K1 follows from K0 and bounded right sides on a slightly larger annulus. These are qualitative class-uniform constants; the proof supplies no numerical K0.

I143's global domain data include a diameter bound D0 and a common single, one-sided graph radius rho and curvature bound G/rho at **every** boundary point, not merely at the pole. Finite covering away from a smaller pole ball uses those data and the positive lower bound on |x|, as well as D0^A,D0^B for upper coefficient bounds. A packing cover has a bound depending on n,D0/rho after the stated shrinking. Holes and non-star-shaped domains are allowed; two arbitrarily close boundary sheets with no common one-sided chart are not. A pole chart alone does not numerically control the away-pole problem over arbitrary varying domains. This is an input distinction, not a failure of the original fixed-domain assertion.

### 1.3 H143, including unbounded solutions — PASS without repairs

Let `gamma_w=(n+A)/(p+1)+(n+B)/(q+1)-(n-2)>0` and `sigma=alpha+beta+2-n>0`. The exact identity is `gamma_w=(1-1/(p+1)-1/(q+1))sigma`. All-radius annular bounds yield

`U<=K0 r^-alpha`, `V<=K0 r^-beta`, `|grad U|<=K1 r^(-alpha-1)`, `|grad V|<=K1 r^(-beta-1)`.

These bounds do not require initial global boundedness. Continuity on the closed half-space bounds each compact half-ball. Since A,B≥0, the sources are locally bounded there. Zero-trace local boundary estimates give bounded gradients and U,V=O(x_n) near the origin, including nonintegral positive weights. No positive value at the boundary pole is required. The inner nonlinear surface terms tend to zero at least as rho^(n+A) and rho^(n+B) times bounded powers; the gradient surface terms also vanish. Singular homogeneous profiles lacking continuity at the pole are outside this statement.

The identity `A-(p+1)beta=B-(q+1)alpha=-n-sigma` makes both cross energies and the absolute gradient product integrable at infinity, with tails bounded by constants times R^-sigma. Cross multiplication of the two equations gives F=I=G after the inner and outer limits. Terms containing U or V vanish on the plane. The cross Pohozaev identity has its plane term zero because x·nu=0, **not** because the normal derivatives are zero. Its sphere terms are O(R^-sigma). Thus `gamma_w F=0`, while positivity on an interior ball gives F>0. H143 follows at its entire stated, possibly unbounded, origin-continuous scope.

### 1.4 Three scales, finite Pohozaev, elimination and normalization — PASS without repairs

The concentration scale is lambda=M^-1, where `M=max(u^(1/alpha)+v^(1/beta))`; the pole distance is |x0|; the physical boundary distance is dist(x0,partial Omega). They cannot be identified. Away-pole bounds force x0 toward the pole for a divergent sequence. The annular bound gives `|z|=|x0|/lambda<=T=max(1,K0^(1/alpha)+K0^(1/beta))`. Normalization gives U,V≤1 and one component at z at least `m0=min(2^-alpha,2^-beta)`. A common gradient bound L0 on B_(T+3) gives `dist(z,partial D_lambda)>=kappa=min(1,m0/L0)` by following a segment to a nearest boundary point when its distance is below one. Both coefficient limits are positive; the spatial weights remain |y|^A,|y|^B.

The exact chart bounds are `|psi_lambda|<=G lambda |y'|²/(2rho)`, `|grad psi_lambda|<=G lambda |y'|/rho`, `|D²psi_lambda|<=G lambda/rho`. The flattened divergence matrix differs from I by O(G lambda R/rho), with derivative O(G lambda/rho), and coefficient oscillation is bounded by H(lambda R)^theta. In I143's finite identity Euclidean coordinates are retained, so no flattening error is silently omitted from that identity.

Write F,G,I and f_e,g_e exactly as in the original report. Direct divergence gives

`F=I-int_boundary V partial_nu U-int f_e V`,

`G=I-int_boundary U partial_nu V-int g_e U`,

`cA F+cB G-(n-2)I = B_nonlin-B_grad+int(f_e y·grad V+g_e y·grad U)`.

Indeed the divergence of `y(grad U·grad V)-(y·grad V)grad U-(y·grad U)grad V` is `(n-2)grad U·grad V-(y·grad V)Delta U-(y·grad U)Delta V`. This fixes all signs. On the physical boundary its normal component is `-(y·nu)partial_nu U partial_nu V`. On a graph the numerator of y·nu is `y'·grad psi_lambda-psi_lambda`, up to orientation, bounded by a constant times G lambda |y|²/rho. No star-shaped sign is needed.

At suitable radii in [R,2R], sphere terms are O(R^-sigma). One can use coarea and weak normal traces on almost every truncated domain, with smooth cutoff approximation; no high-dimensional Sard theorem for a merely C² radial restriction is needed. The physical-boundary radial integral is `1+int_1^(2R)t^-sigma dt`. It is logarithmic at sigma=1. The coefficient errors, treated as additive right sides without differentiating a,b, have radial integral `1+int_1^(2R)t^(theta-sigma-1)dt`, logarithmic at theta=sigma. For R≥2 these are bounded respectively by a constant times R and by a constant depending on theta times R^theta. The original finer integrals are retained before these coarse bounds.

Let `dF=F-I` and `dG=G-I`. Then I differs from (F+G)/2 by `-(dF+dG)/2`, while F-G=dF-dG. Substitution in the displayed identity yields exactly the original `gamma_w(F+G)/2` with only the paid errors, including the coefficients n-2 and |cA-cB|. Therefore F143 holds with its stated dependency on n,p,q,A,B,c,C,theta,G,H rho^theta,K0,K1,L0,sigma^-1, independent of lambda,R and the solution. No class-uniformity as the gaps vanish, H grows, rho collapses or pq→1 follows.

For N143, `h=min(kappa/4,m0/(4L0),1/4)` gives an interior ball B_h(z); one component stays at least m0/2. Because the pole belongs to the boundary, |z|≥kappa, hence |y|≥kappa/2 on that ball. Integrating the appropriate one of F or G gives exactly the original

`e0=c omega_n h^n min{(kappa/2)^A(m0/2)^(p+1),(kappa/2)^B(m0/2)^(q+1)}`.

There is no assumption of two center lower bounds. First choose R_* using T,C0,gamma_w,e0,sigma; then choose lambda using the chart, curvature and Hölder restrictions. Renaming a radius in [R,2R] requires the already stated fixed enlargements. Zero G or H deletes the corresponding restriction. Together with the away-pole bound, this bounds M and then `sup(u+v)<=M^alpha+M^beta`. It is a qualitative bound plus a finite-scale reduction relative to K0, not a numerical evaluation of K0.

### 1.5 Preserved scopes

The I143 audit of original I140 remains scoped: the actual p-harmonic affine lift obstruction is existential at large p; p=d and p=2 are not counterexamples. The affine cubic estimate depends on a section modulus and the completeness/dimension-ten distinctions persist. C140 is an interior non-effective estimate with both gaps. V140 uses radial logarithmic derivative budgets, not merely Hölder coefficients. O140a has nonzero boundary data and lacks the unweighted strict gap; O140b loses a common Hölder modulus; O140c is pq=1 resonance. None refutes the present target. No correction to any original claim is made here.

The original I125 literal canonical-inventory FAIL, its distinct ordering-only adapter PASS, and the I122 literal general-Lambda equality FAIL are preserved separately. No inherited seal, receipt, theorem scope or parked branch is repaired or promoted.

## 2. Numerical input and what an effective result would mean

For a numerical assertion one may supply n as an integer, p,q,A,B,theta,c,C,H and geometry bounds by computable real names (rational interval oracles of prescribed error), together with certified positive rational lower bounds for p-1,q-1,c,theta,gamma0,gamma_w and rho. Upper bounds for the remaining finite parameters are supplied rationally. Equivalently one may search the real oracles for such strict lower bounds; termination follows only from the specified strict hypotheses. Plain arbitrary real symbols without a computable representation do not define an evaluable bound. A,B may be zero; no decision of exact equality is required when restrictions are written using upper bounds and 1+G,1+H.

For a full-domain result the input must also include a finite atlas or certified covering and one-sided graph/collar bounds throughout the boundary, a diameter bound and an away-pole radius. Functions representing charts and coefficients require evaluation oracles and certified derivative/modulus bounds on their stated compact sets. A local pole chart alone is sufficient to describe a local exclusion model, but not a bound uniform over arbitrary global geometry. The estimates below need only the indicated numerical envelopes, not a decision procedure recognizing arbitrary domains from pictures.

Powers, sphere volumes and the definite one-dimensional integrals below are computable with interval arithmetic on this representation. Positive denominators are certified before division; tail errors are given explicitly. **This describes the input of the paid estimates; it does not assert that the complete Target L threshold has been computed.** In particular, no unnamed elliptic constant below is allowed to contain a qualitative Liouville modulus. K0 remains explicitly non-effective wherever it is used.

## 3. Route A: finite-ball Newtonian remainders and the source pressure interface

The complete stipulated six-section weighted proof was read, including origin reduction, source masses, exact potentials, localization, the actual interval proof, all cap/layer/endpoint losses, and the final scaling contradiction. Its lower operations are premises here, not objects of a truth audit. This route tests their transfer to a **finite** domain.

### 3.1 A146: a finite-ball mass and signed harmonic remainder estimate

Let U,V be positive classical solutions in B_L, continuous on compact subballs, with

`-Delta U=a(x)V^p`, `-Delta V=b(x)U^q`, `c<=a,b<=C`, `p,q>1`.

No boundary values on the artificial sphere are prescribed. Write f=bU^q,g=aV^p and use alpha0,beta0. The following estimates do not invoke any Liouville theorem or compactness. Put

`d_n=k_n(2^(2-n)-3^(2-n))>0`, `omega_n=S_n/n`,

`A_f=c omega_n d_n^q`, `A_g=c omega_n d_n^p`,

`C_f=(A_f A_g^q)^(-1/(pq-1))`, `C_g=(A_g A_f^p)^(-1/(pq-1))`.

For 4r≤L,

`int_Br f <= C_f r^(n-2-beta0)`, `int_Br g <= C_g r^(n-2-alpha0)`.       (A146.1)

Proof: the Dirichlet Green function of B_(4r) on B_r×B_r is at least d_n r^(2-n). Indeed K(x-y)≥k_n(2r)^(2-n), while its positive harmonic boundary correction is at most k_n(3r)^(2-n). Positivity of boundary values gives U≥G_(4r)g and V≥G_(4r)f. Integrating the qth and pth powers on B_r gives

`M_f>=A_f r^(n+(2-n)q) M_g^q`, `M_g>=A_g r^(n+(2-n)p) M_f^p`.

Combine, divide by positive masses, and use pq>1. The equality case 4r=L follows by increasing smaller radii to r, so no trace on partial B_L is required. The resulting exponents are exactly those in (A146.1). Hölder's inequality, now legitimately using p,q>1, gives

`int_Br U <= C_U r^(n-alpha0)`, `C_U=omega_n^(1-1/q)(C_f/c)^(1/q)`,

`int_Br V <= C_V r^(n-beta0)`, `C_V=omega_n^(1-1/p)(C_g/c)^(1/p)`.       (A146.2)

Take s=L/8. Define the actual truncated Newton potentials

`P_U(x)=int_Bs K(x-y)g(y)dy`, `P_V(x)=int_Bs K(x-y)f(y)dy`.

Then on B_s, `U=P_U+h_U`, `V=P_V+h_V`, with harmonic **signed** remainders. For |x|≤s/2,

`|h_U(x)|+s|grad h_U(x)| <= D_U s^-alpha0`,

`|h_V(x)|+s|grad h_V(x)| <= D_V s^-beta0`,                         (A146.3)

where, for example,

`D_U=16 n 8^n(C_U/omega_n+k_n C_g)`, `D_V=16 n 8^n(C_V/omega_n+k_n C_f)`

are valid deliberate enlargements.

To prove this, let H_U be the harmonic extension of U from partial B_s and let J_U be the positive harmonic correction in the ball Green kernel. Then h_U=H_U-J_U, with 0≤H_U≤U. Mean values on interior balls and (A146.2) bound H_U on B_(3s/4) by `8^n C_U s^-alpha0/omega_n`; harmonic differentiation on balls of radius s/4 bounds its gradient on B_(s/2). The ball correction kernel is explicitly

`k_n s^(2-n) [1-2x·y/s²+|x|²|y|²/s^4]^((2-n)/2)`.

Its value and first x-derivative on |x|≤s/2, |y|≤s are at most `k_n 2^(n-2)s^(2-n)` and `k_n(n-2)2^(n-1)s^(1-n)`. Integrate against (A146.1). These estimates give (A146.3) with the stated D_U,D_V. Thus the artificial-boundary correction is retained and paid. Setting the remainder equal to zero would be false for a finite ball. No lower bound on unknown sphere data is used.

The finite dyadic sum also gives the source's required truncated-potential bound on B_2 for s≥8. For example each annulus 2^j≤|y|<2^(j+1), j≥3, contributes at most

`k_n 2^(n-2) C_g 2^(n-2-alpha0) 2^(-j alpha0)`

to P_U; the geometric series is bounded explicitly by its first term divided by `1-2^-alpha0`. The near part outside |x-y|<ell is at most `k_n ell^(2-n) C_g 8^(n-2-alpha0)`. The f-potential uses beta0. Radii needed here are at most 2s=L/4, so every mass bound used is within the available domain. This pays local masses, local L1 values and far potentials without sending an artificial boundary to infinity.

### 3.2 What truncation changes in the complete pressure operation

Let f_s,g_s be f,g on B_s and zero outside. Retain the source cutoffs eta,w,X supported in B_2, and define `d pi_s=f_s(x)g_s(y)K(x-y)dxdy`. Its marginals on B_2 are exactly f(U-h_U) and g(V-h_V). For any bounded cutoff zeta there,

`|int zeta fU-int zeta d(pi_s)_x| <= ||zeta||_infty C_f 2^(n-2-beta0) D_U s^-alpha0`,       (A146.4)

with the analogous g,V estimate. The virial acquires the signed term `-int f X·grad h_U-int g X·grad h_V`, bounded by

`||X||_infty [C_f 2^(n-2-beta0)D_U s^(-alpha0-1)+C_g 2^(n-2-alpha0)D_V s^(-beta0-1)]`.       (A146.5)

These are additive errors independent of the particular solution, not a claim that the truncated marginals equal the nonlinear energies.

For a retained interval I inside the cap annulus, Tonelli recovers the endpoint average of P_U, which is `Ubar_I-hbar_(U,I)`. The pressure defect for U therefore differs by `h_U(x)-hbar_(U,I)`. If |I|≤2 delta d(x), its absolute value is at most `2 delta d(x) D_U s^(-alpha0-1)`. Integration in levels costs at most

`2 delta D_U s^(-alpha0-1) ||d h_e||_infty C_f 2^(n-2-beta0)`,       (A146.6)

and similarly for V. Source-layer components meeting the artificial sphere have zero retained weight: a positive infimum of h_e forces the whole component and its endpoints into 1<|x|<2. All truncated layer/partner integrals are nonnegative before subtraction. Thus a discontinuity of f_s at |x|=s cannot create an unaccounted positive-weight endpoint.

The source's local mass, potential and layer estimates can now be followed with these additional terms. In particular both copies of the averaged layer loss remain. The correct parameter order is: fix an error budget using the strict gamma0 margin; choose the angular cap kappa; choose the short-interval delta after kappa; choose the level threshold P after both; choose the localization delta (or a smaller common delta) to pay the marginal error; only then choose the outer-ball ratio s large enough for (A146.4)–(A146.6). Choosing a ball size first and later allowing cap constants to diverge would not prove a numerical estimate.

More precisely the closing budget is `epsilon<=gamma0/[4(n-1+|c1-c2|/2)]`, where `c1=n/(q+1)-(n-2)`, `c2=n/(p+1)`. The three source relative losses have form `C kappa+C_kappa delta+C_(kappa,delta)/P`; the new remainder losses have explicit mass factors above. The gap is gamma0, not gamma_w, in this secondary unweighted model.

**Limit of this route's completed result.** Equations (A146.1)–(A146.6) are proved numerical finite-domain estimates. They remove a specific missing hypothesis of a naive finite-ball transfer. I have not assembled a certified numerical majorant for every cap-profile derivative, localization constant, and the complete resulting pressure bound, nor a numerical boundary analogue. Writing an unnamed `C_press(gamma0)` and calling it effective would not meet the task. Conditional on such a computed energy bound E≤C_press, a normalized center U(0) or V(0)≥m has an explicit lower energy: on B_2 with U,V≤1, elementary local Newton/harmonic differentiation gives a permissible `Q=100 n 2^n(1+C)` for both gradients on B_1; put `h=min(1/4,m/(2Q))` and

`e=c omega_n h^n min{(m/2)^(p+1),(m/2)^(q+1)}`.

Then E on B_1 is at least e. Scaling by R would give `R^sigma0 e<=C_press`, sigma0=alpha0+beta0+2-n>0, provided the scaled finite ball still has the required outer ratio. One would first choose `R>(C_press/e)^(1/sigma0)` and then L sufficiently larger than R. This is a precise conditional interface, **not a completed effective finite-ball exclusion**. No grid, finite sample, formal compactness theorem or least finite constant replaces that missing calculation.

### 3.3 Hölder endpoints, physical boundary and coefficient errors

There is a second concrete modification. For theta<1 the original retained length `2 delta inf_I d` gives a coefficient endpoint error proportional to `delta^theta d^theta U`. Multiplication by w does not make it bounded by a constant times eta U, since `d^theta w/eta` can grow like d^(theta-1). This is a failure of that direct **bookkeeping substitution**, not a failure of I143 or of Target L.

A valid retention rule is

`|I|<=2 delta (inf_I d)^(1/theta)`,

with `0<delta<=min(1/4,theta/8)`, and test length `ell=delta d^m`, where `m>=max(n+3,1/theta+1)`. The 1-Lipschitz property of d gives `(1-delta)^(1/theta)>=1/2`, so every component of length≤ell passes the new rule. For positive coefficients bounded below by c,

`|b(z)^(-1/q)/b(x)^(-1/q)-1| <= C(p,q,c,C) H |z-x|^theta`.

On a retained component this is at most `C H delta^theta d(x)`. Annular weight variation contributes `C delta d(x)` as before. Thus the full endpoint error is `(C delta+C H delta^theta)d U`, paid by d w≤C eta. Use `k=n(m+1)`, `N=k+n+2`; then the high-level long-interval loss is still proportional to P^-1 d^N, the low-level power is N-1-k=n+1, and the localization far exponents are `2m+2n+1` and `m+2n+2`, positive. Cap oscillation has exponent `N-n-1+m>=N`. This proves the needed endpoint and length bookkeeping, without differentiating Hölder coefficients. It is a separately labelled new operation, not a retroactive repair of the original C¹ weighted pressure proof.

It does not alone replace the virial identity: for merely Hölder a,b, freeze coefficients and retain additive PDE errors. On any normalized finite model U,V≤1 in D_lambda∩B_(4R), with a known gradient envelope L_R on B_(2R), the raw errors obey

`|int(f_e V+g_e U)| <= H lambda^theta S_n sum_(W=A,B) (2R)^(n+W+theta)/(n+W+theta)`,

`|int(f_e y·grad V+g_e y·grad U)| <= H lambda^theta L_R S_n sum_(W=A,B) (2R)^(n+W+theta+1)/(n+W+theta+1)`.

The physical-boundary contribution on a one-sided pole graph is at most

`C_n (G lambda/rho) L_R² (2R)^(n+1)`.

Here the geometric constant is an explicit graph area bound once slope≤1/10 is fixed. These are direct volume/area integrations, not a nonlinear stability theorem. On exact flat half-balls L_R can be supplied by signed odd **linear Poisson** extension and local differentiation from bounded normalized sources; no positive whole-space nonlinear conclusion follows. On curved charts a numerical boundary regularity envelope must also be supplied or extracted. These raw estimates show the order of choices—R first, lambda second—but do not make the artificial-sphere energy small as R grows. The missing effective unweighted half-ball exclusion is essential for K0; a full-ball result alone would not settle secondary centers near the physical boundary.

## 4. Route B: preserve reflection cancellation before localization

### 4.1 B146: a joint vector bound with no K/G loss

For x,y in H set a=x_n,b=y_n and `Q_t=|x-y|²+4tab`. The exact positive representation is

`G(x,y)=(2ab/S_n) int_0^1 Q_t^(-n/2)dt`.                         (B146.1)

It follows either by one integration or from the heat-kernel representation

`G=int_0^infinity (4pi t)^(-n/2) exp(-|x-y|²/(4t)) [1-exp(-ab/t)]dt`.

These identities are proved kernel formulas, not a proposed nonlinear heat-flow argument.

Let X be a Lipschitz vector field on the closed half-space, tangent on its plane, with Lipschitz seminorm L. Then for distinct x,y in H,

`|(X(x)·grad_x+X(y)·grad_y)G(x,y)| <= (n+2)L G(x,y)`.             (B146.2)

Proof: put `S=X_n(x)/a+X_n(y)/b`. Tangency and the Lipschitz bound give |S|≤2L. Also

`(D_X Q_t)/2=(x-y)·(X(x)-X(y))+2tab S`,

so `|D_X Q_t|<=2L Q_t`. Differentiate the positive integrand in (B146.1). Its logarithmic derivative is `S-(n/2)D_X Q_t/Q_t`, bounded by (n+2)L. Integration proves the assertion. For X=x, S=2 and D_X Q_t=2Q_t, giving D_X G=(2-n)G **exactly**. Thus the n-2 coefficient survives joint dilation without separately estimating either Newton kernel.

For compact tangent fields the estimate is integrable against the positive interaction whenever its relevant marginals are finite. It is applicable to bounded normalized solutions on finite models and to truncated positive sources, not only to singular abstract densities. It improves the crude K/G blowup from independent estimates. It is still an O(E) bound, whose coefficient cannot be made arbitrarily small by naming the cap radius. In particular, (B146.2) does not pay the strict gamma_w budget.

### 4.2 C146: boundary first moments and the actual artificial-boundary remainder

Let 0≤U≤1 solve -Delta U=g≥0 in B_L^+, with continuous zero data on the physical disk; g is locally bounded up to that disk. This includes every normalized target pair on an exact flat finite half-ball: g=a|x|^A V^p, and analogously f. No annular K0 is assumed. For 2r<L define

`M_1(g,r)=int_(B_r^+) y_n g(y)dy`.

Then

`M_1(g,r)<=M_n r^(n-1)`, `M_n=2^(n+6)(n+6)omega_n`.             (C146.1)

Use the nonnegative test function `phi=y_n(1-|y|²/(4r²))_+³`. It and its first derivative vanish at the artificial sphere, and phi=U=0 on the plane. Integration by parts therefore has no physical or artificial boundary term. On B_r^+, phi≥(27/64)y_n. Direct radial differentiation gives

`|Delta phi| <= (3/2)(n+6)y_n/r²` on B_(2r)^+.

Since U≤1, integrating this bound proves (C146.1), with the deliberately larger stated M_n. The operation uses positivity and bounded normalization, not a whole-space source-mass lower bound.

Take s<L/4 and set

`P_U^H(x)=int_(B_s^+) G(x,y)g(y)dy`.

There is a harmonic signed remainder `h_U^H=U-P_U^H` on B_s^+, zero on its disk, with the explicit estimates

`|h_U^H(x)| <= B_n x_n/s`, `|grad h_U^H(x)|<=B_n/s`,  |x|≤s/2,    (C146.2)

where one permissible enlargement is

`E_n=2^(2n+8)n²(1+k_n)`, `B_n=4n+E_n M_n`.

Here is the boundary contribution rather than its deletion. Let H_s be the harmonic extension of the actual U sphere data with zero disk data. The half-ball Green potential W_s satisfies 0≤W_s≤U and H_s=U-W_s, so 0≤H_s≤1. Odd reflection of H_s alone is bounded harmonic in B_s; elementary harmonic differentiation gives `|grad H_s|<=4n/s` in B_(s/2), and integration from the plane gives `H_s<=4n x_n/s`.

The half-ball Green kernel is the difference of two **ball** Green kernels. Consequently `J_s=P_U^H-W_s` is the positive reflected ball correction. Its kernel is

`k_n s^(2-n) {Q(x,y)^((2-n)/2)-Q(x,Ry)^((2-n)/2)}`,

`Q(x,y)=1-2x·y/s²+|x|²|y|²/s^4`.

For |x|≤s/2, |y|≤s all denominators on the interpolating segment are at least 1/4, and the two Q's differ by 4x_n y_n/s². The mean-value formula, and its first x-derivative, give

`0<=correction<=E_n x_n y_n s^-n`, `|grad_x correction|<=E_n y_n s^-n`.

The displayed E_n exceeds the resulting first and mixed second derivative bounds of Q; only powers of 2 and n are involved. Integrate using (C146.1). Since h_U^H=H_s-J_s, this proves both estimates in (C146.2). The same bound applies to V. The actual harmonic remainder can have either sign; its normal derivative is controlled, not set to zero.

There is also a finite-tail form. For |x|≤R/2 and |y|≥R,

`G(x,y)<=C_n x_n y_n |y|^-n`, `|grad_x G(x,y)|<=C_n y_n |y|^-n`,

with, for example, `C_n=2^(2n+8)n²(1+k_n)`. Divide R<|y|<s into dyadic annuli and apply (C146.1) at the outer radii (all at most 2s). The integral tails are bounded by

`2^n C_n M_n x_n/R` and `2^n C_n M_n/R`, respectively.           (C146.3)

The series is geometric with ratio 1/2, so it comes with an explicit remainder bound. The same proof applies to an infinite bounded normalized model, without assuming an unweighted total source mass. At x_n=0 its normal kernel derivative is

`partial_(x_n)G((x',0),y)=2y_n/[S_n(|x'-y'|²+y_n²)^(n/2)]`.

Thus (C146.3) controls the plane derivative tail as well; zero Dirichlet data alone would not do so. This is a genuine first-moment tail estimate in the actual normalized PDE class.

### 4.3 Radial cap/layer difficulty after the remainder has been paid

The new estimates resolve a far-tail and artificial-boundary problem but not the finite radial pressure inequality. The exact signed radial interaction in I143 §3.3 must be localized into a pressure term recoverable from nonlinear layers. Formula (B146.1) contains the product x_n y_n in both the prefactor and denominator. For non-tangential e, along x=z+se and y=z'+te the image pair is `z+se-Rz'-t Re`. The sum of the two midpoint integrations contains

`[(s-m_I)e-(t-m_J)Re]·grad K(x-Ry)`.

When e_n≠0, this contains a sum-parameter contribution as well as a difference-parameter contribution. Neither the two-interval trapezoid in s-t nor the tangential J_e operation accounts for it. Choosing Re for the partner instead makes the *direct* kernel lack the required parallel-line structure. Both kernels share that structure only if Re=e. This is an algebraic obstruction to applying the original interval operation unchanged, not a counterexample to a new paired-reflection inequality or to Target L.

Tangential directions do have the paid inequality from §1.1, but their caps do not approximate all radial directions on the half-annulus. Conversely, merely applying (B146.2) to the missing terms gives a fixed multiple of E, which need not fit an arbitrarily small positive gamma_w. Joint homogeneity supplies n-2 only for eta=1 and does not supply the cutoff pressure sign. Replacing n-2 by n in the final hyperbolic margin would change the theorem and is not allowed.

There is a quantitative small-plane-layer bound for the normalized class, but it does not close this gap. If a known boundary gradient envelope Q_R holds on B_(2R)^+, then U,V≤Q_R y_n there. For 0<tau<R, for example,

`int_(B_R^+ intersect {y_n<tau}) g <= C R^A Q_R^p omega_(n-1) R^(n-1) tau^(p+1)/(p+1)`.

On y_n≥tau, ordinary source mass is bounded by `tau^-1 M_1(g,R)`. Both estimates are for actual bounded sources, not unrestricted singular densities. They can pay an **additive** discarded layer at a fixed R. However Q_R and the bounded normalization change under the dilation used in the pressure contradiction. The smallness of this discarded layer relative to the dilated nonlinear energy is not proved here. The corresponding cap mismatch, the reflected sum-parameter endpoint term, and the small-potential/near-plane errors therefore cannot yet all be assigned a common `epsilon E+C_epsilon` budget compatible with gamma_w.

The finite-scale target left open is a cancellation-preserving localization and layer inequality on normalized B_L^+ models, combining (C146.2)–(C146.3) with the exact radial vector identity, whose **total** relative coefficient is below gamma_w/4 after explicit choices, and whose additive term is numerically controlled independently of the solution. It must then survive the raw coefficient and curvature errors in §3.3 with R chosen first. No such complete inequality is asserted in this report. A numerical grid would additionally need a regularity covering net, residual tolerance, coverage of all normalized functions and a compactness-free termination certificate. None is supplied by finite kernel samples, and no such grid is used.

### 4.4 Full primary operations and why they do not supply the missing number here

The complete 14-page [Li–Souplet v2](https://arxiv.org/abs/2408.17007v2) was read through its proof ending and references. It establishes unweighted half-space nonexistence for solutions bounded on every finite strip. The operative chain is normal monotonicity, comparison of components, the nonlinear strip maximum principle, a logarithmic derivative estimate, a modified normal-convexity argument, and a local-mass contradiction. It is not a weighted radial pressure theorem.

One quantitative part is explicit in its Lemma 4.4: for `A^{-1}div(A grad xi)>=(xi_+)^k`, with xi≤0 on the two strip faces and a tangential cutoff supported in radius 2R, its tested inequality is

`(int A(xi_+)^((k-1)m) psi^(2m))^(1/m) <= ||grad psi_1||² m²/[R²((k-1)m-k)] (int_annulus A)^(1/m)`.

For bounded A and fixed strip height, m≈R yields an O(1/R) factor times a completely displayed mass root. This is a useful numerical operation **when its boundary signs and derivative weight are available**. In a finite half-ball the artificial top/lateral data need not give the required signs. The preceding moving-plane start/continuation and component comparison in the paper concern infinite strips/half-space; no uniform finite-cylinder error is furnished there.

The convexity proof also constructs phi using `h(R)=sup_GammaR(|grad U_n|/U_n+|grad V_n|/V_n)`, via a double integral of `exp(-t)/(1+hhat(t))`, plus a cubic cutoff around a negative witness. Its integral has a simple exponential upper tail, but evaluating the denominator uniformly requires the preceding derivative-ratio bounds and monotonicity. These are not furnished for all normalized finite-domain models merely by U,V≤1. Treating h as an unnamed elliptic constant would hide the missing operation. The sign-changing odd extension in that paper is used for linear derivative estimates, not to invoke a positive entire nonlinear theorem. I have neither imported that shortcut nor promoted the paper's qualitative conclusion to a numerical constant.

The entire [Dai–Peng paper](https://doi.org/10.1007/s43034-021-00158-1) was read: harmonic remainders, integral representation, Kelvin identities, the start and continuation of scaling spheres, cone lower bounds, and their bootstrap to the integrability contradiction. The continuation explicitly uses the solution-dependent positive minimum in (3.37) and a continuity step in (3.38), after local L^(n/2) smallness. More fundamentally, both individual Kelvin signs are assumed. At n=5,A=B=0,p=4,q=7/5 the two target gaps equal 1/12, but p exceeds 7/3; its Corollary 1.8 does not cover this target point. Its method therefore cannot simply replace the full-hyperbola half-ball operation by constant extraction.

The complete PQS system/doubling proofs, Phan's complete Section 4 and operative Pohozaev reduction, and Quittner–Souplet's complete Section 7.2 were also read. They explain I143's K0 and normalization mechanism, including unequal amplitudes and the physical/free boundary split. Their contradiction/limit steps are not quantitative finite-radius certificates. Comparison with these complete operations supports a technical classification for the present partials; absence of an identical sentence is not a novelty result.

Current version checks on 2026-10-10 confirm Li–Souplet v2 (5 June 2025), Phan v1 (5 August 2011), and Quittner–Souplet v2 (26 September 2024; journal reference Rev. Mat. Complutense 38 (2025), 1–69). The PQS author PDF remains available. The DOI web retrieval returned `Internal Error ()`; the inherited Dai–Peng author PDF/text remains the proof source. Current page bytes are frozen separately. No new success is inferred from a failed DOI request, and no worldwide search/priority claim is made.

## 5. Final mathematical disposition and evidence limits

The new paid estimates are A146.1–A146.6, the Hölder-compatible retention rule, B146.1–B146.2 and C146.1–C146.3. They apply to bounded normalized finite-domain models where indicated and retain harmonic/artificial-boundary and plane derivative terms. The source's exact radial coefficient, both target gaps, coefficient common modulus, three distinct scales and geometry losses are preserved. Negative weights, missing unweighted gap, pq=1, changing coefficient modulus, arbitrary singular half-space functions and frozen-weight dimension reduction play no role.

The original qualitative Target L deduction and F143/N143 remain intact. Neither a fully numerical unweighted boundary annular K0 nor the full reflected radial pressure budget has been obtained. Consequently the translation `sup(u+v)<=M^alpha+M^beta` still has no numerical M furnished by this report. **PARK, no ninth nomination, no acceptance-count change.** The method limitations are not counterexamples to Target L. No formal, human-review or worldwide-priority certification is claimed.

The evidence verifier performs one flat traversal of the immutable 13,223-entry tree, 749 manuscripts, 10,373 originals and all 776 PDF/text bindings per invocation; it does not copy the corpus, re-extract PDFs or run ancestor verifiers/diagnostics. All immutable bytes, original contexts, ancestor seals, receipts and new artifacts are checked before new diagnostics. Only the four explicitly named live ledgers may drift; snapshots may not. Exact owned inventory is globally sorted and prevalidated before a single exclusive seal. Read ranges use Python splitlines and LF-joined passage hashes without an appended LF. HTML text uses the inherited deterministic extractor and final LF. Lexical records are exact multisets with path, line, zero-based start/end columns, matched text and full line over the union of actually read lines; they do not certify semantic coverage.

The offline audit hook denies network, subprocesses, file mutation, bytecode generation, repair and resealing. New diagnostics check finite algebra, exponents and explicit sample identities only. Neither their success nor the evidence replay certifies PDE estimates for all functions, regularity theory, external proofs, contribution or acceptance.

Run `PYTHONDONTWRITEBYTECODE=1 python3 -B frontier/experiments/i146_effective_boundary_exclusion/verify.py`.
