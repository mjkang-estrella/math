**I30 — fresh independent full-proof review, round 2**

**Verdict: PASS, without mathematical repairs, relative to the stipulated corpus.** The submitted theorem has the stated hypotheses and exponent. The proof controls the original metric, not merely a positive-time limit. No additional initial curvature, injectivity, volume, diameter, or harmonic-coordinate assumption is needed. The details below independently reconstruct the analytic estimates, the two-metric bridge, and the fixed-model elliptic argument. They expand valid steps in the candidate; they do not replace a false step or weaken the theorem.

This is a proof verdict only. Substantial-versus-technical significance is reserved for the separate review requested by the parent. No priority, acceptance-count, optimal-exponent, effective-threshold, or attracting-flow claim is made.

The controlling candidate is [I30](../iterations/i30-einstein-metric-stability.md), SHA-256 `a8bdb8937745dc57d89d5ee1562299a8a7d888f1e6816c833f28776a14ebe8a9`. All proofs in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. I read AGENTS.md, the ledger, the full candidate and original author brief, the full I27 report and its original assignment, the parent preliminary note, contracts, manifests, the complete EG proof, the classification interfaces, and the primary passages recorded in [read-passages.json](../sources/i30_einstein_metric_stability_r2/read-passages.json). The author and I27 sources were reused read-only. No complete corpus cache was copied.

**1. Exact statement and dependency contracts.**

There exist universal constants ε,C>0 such that every smooth closed connected simply connected four-manifold (M,g) with sec(g)≥0,

\[
\frac{1}{\operatorname{Vol}_g(M)}\int_M R_g\,d\mu_g=12,
\qquad D=\int_M|\operatorname{Ric}_g-\tfrac14R_gg|_g^2\,d\mu_g<\varepsilon
\]

satisfies

\[
\min_{(N,h)\in\mathscr H}d_{GH}((M,d_g),(N,d_h))\le C D^{1/16},
\]

where the three members of ℋ are the unit round S⁴, CP² with twice the unit-Hopf Fubini–Study metric, and the product of two round spheres of curvature 3. Each has Ric=3h. The defect is not divided by volume. Put η=√D.

The imported contracts are as follows; all later estimates are proved below.

- EG, `prop:initial`, `prop:initial-sobolev`: for sufficiently small η, universal positive lower and upper volume bounds, an upper diameter bound, an initial Sobolev constant, and ‖Ric−3g‖₂²≤5η². The actual proof provides fixed smallness thresholds, not merely a normalization depending on each sequence.
- EG, `prop:weighted`, `prop:tail`, `lem:noncollapse`, `prop:smoothing`: a universal smooth unnormalized-flow interval [0,T], T<1/6; R(t)≥0; uniform Sobolev and ball-volume bounds; |Rm(t)|≤A/t. These are established before positive-time compactness.
- EG, `prop:einstein-defect`: its energy proof gives the quantitative estimate ‖L(t)‖₂≤Cη for L(t)=Ric(g(t))−λ(t)g(t), λ(t)=3/(1−6t), uniformly on [0,T]. The displayed proposition is sequential; the quantitative inference is justified in paragraph 2 below.
- EG, `prop:sectional-defect`, `prop:limit`: every sequence η→0 has a subsequence converging smoothly at all positive times, under time-independent global diffeomorphisms, to (1−6t)h on a closed simply connected N, with Ric(h)=3h and sec(h)≥0. This contract says nothing about the original distances.
- E0, `cor:nonnegative-classification`, including its boundary splitting proof, and E+, `lem:model-curvature` and global classification: the normalized simply connected limit is exactly one of ℋ. E0, rather than a strict-positive statement alone, includes the product.
- Gursky–Viaclovsky, [1105.4648v2](https://arxiv.org/abs/1105.4648v2), equation (3.29), Propositions 7.7 and 7.9 and the latter's full proof: on TT tensors Ric′=−Δ_L/2. At Ric=3h, CP² has spec(−Δ_L)⊂[16,∞); the product has a one-dimensional zero eigenspace and all remaining eigenvalues at least 12. These are spectral statements for the second-order Lichnerowicz operator, not an application of their quadratic-functional stability theorem.

The [review contracts](../sources/i30_einstein_metric_stability_r2/contracts.json) and retained passages identify the hypotheses and downstream uses. The original 34-file pin manifest carries immutable raw GitHub URLs, Git blob identities and SHA-256. The review verifier independently checks these identities against the complete preprint tree.

**2. Uniform constants extracted from EG.**

This quantifier issue is substantive: constants that were allowed to depend on an arbitrary sequence would not prove the theorem. EG's proof fixes them from dimension and the normalization.

The initial almost-Schur calculation gives ‖R−12‖₂≤4η. Orthogonal trace decomposition gives ‖Ric−3g‖₂²≤5η². Chern–Gauss–Bonnet, χ(M)≥2 and |Rm|≤C₀R imply

\[
2\le C(144V+16\eta^2).
\]

Choose a fixed threshold on η to obtain V≥v₀>0. EG's segment argument has error δ≤CV^{-1/2}√5η. Choose a further fixed threshold so δ≤1/4. Its index-form inequality then bounds the diameter by a fixed D₀; Bishop comparison supplies V≤V₀. The initial Sobolev proof depends only on these bounds. No threshold is chosen separately for each metric.

Fix the weighted Sobolev constant S₁ from those initial constants. Choose K₀=12C₀, K′=C_qK², and T<min{1/6,1}, with K bounded on [0,T]. Write w=(|Rm|−K)_+. Initially ‖w(0)‖₂≤4C₀η. To avoid confusing two small parameters, call the fixed tail-absorption threshold δ_tail. First choose δ_tail so the scalar-weight term CS₁δ_tail‖f‖₄² can be absorbed. This fixes an unweighted Sobolev constant S₂. Decrease δ_tail to satisfy the tail-energy and L-energy absorption inequalities with this same S₂. EG obtains

\[
Y_w'(t)\le C_wY_w(t),\qquad
Y_w(t)\le 16C_0^2e^{C_wT}\eta^2
\]

on existing times, by excluding the first crossing of δ_tail. All constants on the right are already fixed.

The Sobolev cutoff iteration supplies a fixed v_* in Vol B(x,r)≥v_*r⁴ for r≤1. Next fix EG's A>2 with A/T≥max{1,4 sup K}. At a first crossing t max|Rm|=A, rescaling and Shi's estimate give a ball of radius cQ^{-1/2}, Q=A/t, on which w≥Q/2. Its energy is at least v_*c⁴/4. Choosing η so the preceding bound on Y_w is smaller than this fixed number excludes the crossing. The curvature continuation criterion gives a common lifespan strictly greater than T. This is the quantitative reading of EG's “sufficiently large j”; no compactness has been used to obtain the lifespan.

For L, EG uses moving orthonormal frames. In those frames the metric components are constant, λ′=2λ², and

\[
\partial_tL=\Delta L+2\operatorname{Rm}(L)+2\lambda L.
\]

The frame convention matters: in fixed coordinates the Ricci evolution contains −2Ric², which the frame motion cancels. The resulting energy inequality is

\[
Y_L'\le-2\int|\nabla L|^2+C\int(1+w)|L|^2.
\]

Hölder, Kato and the uniform Sobolev inequality bound the w term by CS₂‖w‖₂∫(|∇L|²+|L|²). Our fixed tail threshold absorbs its gradient part, so Y_L′≤C_LY_L. Since Y_L(0)≤5η²,

\[
\sup_{0\le t\le T}\|L(t)\|_{L^2(g(t))}\le C\eta. \tag{R1}
\]

The upper volume bound persists because R≥0. Fix τ=T/2, c(t)=1−6t and \(\bar g(t)=c(t)^{-1}g(t)\), and set k=\(\bar g(\tau)\). Here c(t) is uniformly bounded away from zero. Curvature bounds on [τ/2,τ], Shi estimates, EG's noncollapse and the injectivity estimate used in EG give bounded geometry for k, independent of g. In particular choose r₀ and K fixed so that, for every center and 0<r≤r₀,

\[
\mu_k(B_k(x,r))\ge\omega_4r^4(1-Kr^2)\ge c_*r^4. \tag{R2}
\]

This uses normal coordinates below the fixed injectivity radius. The leading coefficient must be ω₄, not merely an arbitrary noncollapse constant; bounded sectional curvature and the radial Jacobi comparison supply it. Only k has this injectivity bound. For the initial metric, Ric≥0 gives the complementary sharp upper coefficient

\[
\mu_g(B_g(x,r))\le\omega_4r^4. \tag{R3}
\]

**3. Parabolic smoothing and the stopping-time distance estimate.**

Let f=|L|, using regularization at its zeros. The moving-frame equation and Kato give

\[
(\partial_t-\Delta)f\le C(|\operatorname{Rm}|+1)f.
\]

Fix any s∈(0,τ]. On [s/2,s] the potential is at most B/s with B fixed. For p≥2, integration of the scalar inequality yields

\[
\frac d{dt}\int f^p+\frac{4(p-1)}p\int|\nabla f^{p/2}|^2
\le\frac{Bp}s\int f^p. \tag{R4}
\]

The volume derivative is −R dμ, so its contribution is nonpositive. This is why no uncontrolled evolving-volume coefficient enters the iteration.

Choose nested intervals I_j=[t_j,s] with t₀=s/2, t_j↑3s/4 and cutoff derivatives bounded by C2ʲ/s. For v=f^{p/2}, the cutoff version of R4 controls sup∫v² and ∫|∇v|² by C(p+2ʲ)s^{-1}∫_{I_j}fᵖ. The Sobolev inequality and

\[
\int_{I_{j+1}}\!\int v^3
\le\big(\sup_{I_{j+1}}\|v\|_2\big)
       \int_{I_{j+1}}\|v\|_4^2
\]

give, enlarging fixed constants if necessary,

\[
\|f\|_{L^{3p/2}(I_{j+1}\times M)}
\le\left(\frac{C(p+2^j)}s\right)^{1/p}
       \|f\|_{L^p(I_j\times M)}.
\]

Use p_j=2(3/2)ʲ. The sums ∑1/p_j=3/2 and ∑j/p_j=3 are finite. Thus the product of dimensional/Sobolev constants converges and the net time factor is s^{-3/2}. At the terminal time,

\[
\|L(s)\|_\infty
\le Cs^{-3/2}\left(\int_{s/2}^s\|L(t)\|_2^2dt\right)^{1/2}
\le C\eta/s. \tag{R5}
\]

This is a positive-time estimate. It is not asserted at zero.

Independently of η, the curvature bound gives Ric≤B/t. For a minimizing g(t)-geodesic of length ℓ≥2√t, choose the piecewise-linear index cutoff ψ which increases from 0 to 1 over the first √t, is 1 in the middle, and decreases over the last √t. The summed index form gives ∫ψ²Ric(γ′,γ′)≤3∫|ψ′|²=6/√t. On the two endpoint intervals, the upper Ricci bound gives ∫(1−ψ²)Ric(γ′,γ′)≤2B/√t. If ℓ<2√t, the direct bound gives the same estimate. In either case,

\[
\int_\gamma\operatorname{Ric}(\gamma',\gamma')\le C/\sqrt t.
\]

The distance first-variation inequality, interpreted at cut-locus times in the usual barrier/almost-everywhere sense, therefore yields ∂_t d_{g(t)}(x,y)≥−C/√t. For completeness, distance is locally Lipschitz in time on every compact positive interval, and every limiting minimizing geodesic obeys the same bound; multiplicity of minimizers does not affect this lower bound. Integrate from δ to s, then let δ↓0 for the individual smooth initial flow. Its distances converge to d_g and the derivative bound is integrable uniformly. Consequently

\[
d_{g(s)}(x,y)\ge d_g(x,y)-C\sqrt s. \tag{R6}
\]

No Ricci lower bound at positive times is involved.

Differentiating the rescaling, as an equality of covariant tensors in fixed material coordinates,

\[
\partial_t\bar g=-2L/c.
\]

The tensor norm |L/c|_{\bar g} equals |L|_g. R5 thus implies the quadratic-form inequalities |∂_t\bar g|≤Cηt^{-1}\bar g. Integrating lengths and then distances on [s,τ] gives

\[
d_k\ge e^{-C\eta\log(\tau/s)}d_{\bar g(s)}
\ge e^{-C\eta\log(\tau/s)}(d_g-C\sqrt s).
\]

The second inequality uses c(s)^{-1/2}≥1. Set s=η², after imposing η²<τ. Since diam(g)≤D₀ and 1−e^{-z}≤z,

\[
d_k(x,y)\ge d_g(x,y)-a,
\qquad a=C\eta(1+|\log\eta|). \tag{R7}
\]

This never integrates η/t down to zero. The I27 logarithmic objection is respected: the interval [0,η²] is controlled by R6, and only [η²,τ] uses R5.

**4. Volume control for every material measurable subset.**

The four-dimensional volume form is dμ_{\bar g}=c^{-2}dμ_{g(t)}. Since c′=−6,

\[
\partial_t d\mu_{\bar g}
=(-R+12/c)d\mu_{\bar g}
=-\operatorname{tr}_{g(t)}L\,d\mu_{\bar g}. \tag{R8}
\]

The trace is with respect to g(t), not \(\bar g(t)\). Its norm satisfies

\[
\|\operatorname{tr}_{g(t)}L\|_{L^2(\bar g(t))}
\le 2c^{-1}\|L\|_{L^2(g(t))}\le C\eta. \tag{R9}
\]

Fix any measurable U⊂M. Smooth positive volume densities on the compact spacetime interval allow differentiation under its characteristic function for this individual flow. There is no requirement that U have smooth boundary. With V(t)=μ_{\bar g(t)}(U), R8–R9 and Cauchy–Schwarz give

\[
|V'(t)|\le C\eta\sqrt{V(t)}.
\]

If U is null it is null for every smooth positive density and the conclusion is immediate. Otherwise V(t)>0 and division by 2√V followed by integration gives

\[
|\sqrt{\mu_k(U)}-\sqrt{\mu_g(U)}|\le b\eta. \tag{R10}
\]

The constant b is uniform over U and g. No bound on the time-zero supremum of L is used. A subset defined using k, such as a k-ball or the difference of two balls, can be selected after both metrics are fixed and then held fixed in R8. This is legitimate and different from differentiating a moving metric ball.

In particular, R3 and R10 give

\[
\mu_k(B_g(x,r))\le\omega_4r^4+C\eta r^2+C\eta^2. \tag{R11}
\]

This small-set bound cannot be inferred from a total-volume estimate alone. The proof establishes exactly the stronger arbitrary-set statement that the candidate needs.

**5. Independent two-metric reconstruction.**

Everything in this paragraph is a deterministic argument for the two smooth metrics on the same compact set. Its inputs are R2, R3, R7, R10 and the initial diameter bound. It uses neither sectional nonnegativity of k nor any prior two-sided distance comparison.

First, R7 gives the correct inclusion

\[
B_k(z,\rho)\subset B_g(z,\rho+a). \tag{R12}
\]

For x,y let ℓ=d_g(x,y), q=max{ℓ,a,√η}. Assume q is below a fixed small fraction of r₀. On the image Γ of a minimizing initial geodesic, choose a maximal q-separated set in d_k. It is finite: Γ is compact in the common smooth topology. Its open k-balls of radius q/2 are pairwise disjoint. Each lies, by R12, in B_g(x,ℓ+q/2+a)⊂B_g(x,3q). Therefore

\[
N c_*(q/2)^4
\le\mu_k(B_g(x,3q))
\le(\sqrt{\omega_4}(3q)^2+b\eta)^2
\le Cq^4,
\]

so N≤C.

Maximality covers Γ by k-balls of radius q, or radius (1+δ)q if needed to keep the cover open. Restrict these balls to Γ. If the intersection graph had separate nonempty components, the corresponding unions would separate the connected set Γ. Thus there is a finite chain connecting the endpoint-containing balls, with at most N vertices. Adjacent centers are at k-distance at most 2(1+δ)q. The triangle inequality, including the endpoint legs, gives

\[
d_k(x,y)\le Cq\le C(\ell+a+\sqrt\eta). \tag{R13}
\]

The initial geodesic's k-length is never estimated. That is the point of the finite connected-cover argument.

Next fix an initial pair distance ℓ=r, where r≤r₀/10 and a<r/4. By R12, B_k(x,r−a)⊂B_g(x,r). Subtract its R2 volume from R11:

\[
\begin{aligned}
\mu_k\big(B_g(x,r)\setminus B_k(x,r-a)\big)
&\le\omega_4[r^4-(r-a)^4]+C(r-a)^6+C\eta r^2+C\eta^2\\
&\le C(r^6+ar^3+\eta r^2+\eta^2)=:C H_r. \tag{R14}
\end{aligned}
\]

Here 0≤r⁴−(r−a)⁴≤4ar³. The r⁶ term comes from the precise Euclidean coefficient in R2, not from an arbitrary ball-volume lower bound.

If an initial ball B_g(z,R)⊂B_g(x,r) is disjoint from B_k(x,r−a), then B_k(z,R−a) lies in that difference by R12. For R>2a and R−a≤r₀, R2 implies cR⁴≤CH_r. Choose

\[
R=2a+C_1H_r^{1/4}, \tag{R15}
\]

with one fixed C₁ large enough to contradict this inequality. Therefore no such disjoint initial ball of radius R exists. Open balls and a strictly larger C₁ avoid boundary-equality issues. At the scales used below, R<r/4 and R−a<r₀, so all volume estimates are within their domains.

On a minimizing initial geodesic from x to y, take w at distance r−2R from x. Then B_g(w,R)⊂B_g(x,r), and every point in B_g(w,R) is within initial distance 3R of y. The no-hole conclusion gives z in B_g(w,R)∩B_k(x,r−a). Since H_r≥η², increasing C₁ if needed gives R≥√η, as well as R≥2a. Apply R13 to (z,y); its scale is at most 3R and hence lies in the permitted range. Thus

\[
d_k(x,y)\le d_k(x,z)+d_k(z,y)\le r+CR. \tag{R16}
\]

This order of deductions is noncircular: coarse comparison precedes the no-hole argument; both use only the one-sided comparison.

Now set r=η^{1/4}. With a=Cη(1+|logη|),

\[
r^6=\eta^{3/2},\quad
ar^3=C\eta^{7/4}(1+|\log\eta|),\quad
\eta r^2=\eta^{3/2},\quad
\eta^2\le\eta^{3/2}.
\]

The logarithmic factor is harmless because η^{1/4}(1+|logη|) is bounded and tends to zero. Therefore H_r≤Cη^{3/2}, R≤Cη^{3/8}, and R/r≤Cη^{1/8}→0. Also a/r→0. These facts verify, rather than assume, all the smallness conditions above. Replacing r by any ℓ∈[r,2r] changes constants only, so R16 holds with error Cη^{3/8} for all such pairs.

For an arbitrary initial minimizing geodesic of length L≥r, let N=floor(L/r). Partition it into N equal subsegments; their endpoint distances equal L/N∈[r,2r]. By R16 and the triangle inequality,

\[
d_k(x,y)\le L+NC\eta^{3/8}
\le L+C D_0\eta^{1/8}.
\]

For L<r, R13 gives d_k(x,y)≤C(r+a+√η)≤Cη^{1/4}, which suffices for the required additive error. The lower error a in R7 is also O(η^{1/8}). Thus

\[
\sup_{x,y\in M}|d_k(x,y)-d_g(x,y)|\le C\eta^{1/8}. \tag{R17}
\]

The identity relation is a correspondence between the two compact metric spaces, so its distortion proves d_GH((M,g),(M,k))≤Cη^{1/8}. This already supplies a genuine original-distance conclusion before the model-neighborhood argument begins.

**6. Uniform neighborhood entry and the gauge.**

Fix small neighborhoods of the three models modulo diffeomorphisms. They may be taken in C^{4,α} to implement the usual slice construction with spare derivatives, with their resulting C^{2,α} slice radius chosen below. This is a choice of output neighborhood, not an extra hypothesis on the initial metrics: EG's positive-time convergence is smooth.

If no universal defect threshold placed every k in their union, choose a sequence with η_j<1/j outside it. EG's `prop:limit`, at the already fixed τ, gives global diffeomorphisms with k_j converging smoothly to a normalized nonnegative Einstein metric on a closed simply connected N. E0 identifies N,h with one of the three models, contradicting exclusion from its neighborhood. This proves a universal neighborhood-entry threshold. It may be ineffective, which is allowed by the theorem's quantifiers.

On one model (N,h), write δ_hu=−∇ⁱu_{ij}. The pure divergence slice chooses a diffeomorphism φ so that

\[
\phi^*k=h+u,\qquad\delta_hu=0,\qquad\|u\|_{C^{2,\alpha}(h)}<\rho. \tag{R18}
\]

Here is the gauge interface, including its finite-dimensional obstruction. The linearization in a vector field X of δ_h(φ_X^*h−h) is δ_hℒ_Xh. Its principal symbol is elliptic. Since δ_h is adjoint to the symmetric gradient up to the fixed conventional factor,

\[
\langle\delta_h\mathcal L_Xh,X^\flat\rangle_{L^2}
=\tfrac12\|\mathcal L_Xh\|_2^2.
\]

Its kernel is precisely the Killing fields. For every symmetric tensor v, δ_hv is orthogonal to the Killing fields, by integration by parts. Therefore the gauge equation takes values in their fixed orthogonal complement; on that complement the linearization is an isomorphism. The local elliptic slice/implicit-function construction gives R18 and its norm control. One can use a higher regularity input neighborhood as above and bootstrap the equation, so no differentiability-of-pullback shortcut at a critical regularity is required. The remaining isometry ambiguity is irrelevant to existence and distance comparison. There are only three fixed backgrounds, so the constants and radii can be made uniform by taking their minimum/maximum.

The primary source's Lemma 2.10 uses its β gauge and an additional scale variable; it must not be quoted verbatim as R18. Its actual proof explains the finite-dimensional obstruction argument, and Remark 2.15 explicitly discusses the pure divergence alternative. The candidate instead uses the pure divergence construction just described. No scale variable is introduced here; the fixed Einstein constant is retained.

**7. Ellipticity, kernel removal and the fixed-slice rate.**

Let F(q)=Ric(q)−3q and P=DF_h. The pair (P,δ_h) is overdetermined elliptic. To check rather than assume the symbol assertion, take a nonzero covector ξ and rotate so it is a multiple of e¹. The symbol condition δ_hu=0 gives u_{1j}=0. The Ricci principal symbol is

\[
2\sigma(P)(\xi)u=|\xi|^2u+\xi\otimes\xi\operatorname{tr}u
-\xi\otimes u(\xi,\cdot)-u(\xi,\cdot)\otimes\xi.
\]

If this vanishes, its components with indices >1 give u_{ab}=0; thus u=0. Standard elliptic estimates on each fixed compact background give

\[
\|u\|_{H^2}\le C\big(\|Pu\|_2+\|\delta_hu\|_{H^1}+\|u\|_2\big). \tag{R19}
\]

To remove the last term on the slice, examine the full kernel, not just TT tensors. Suppose δ_hu=0 and Pu=0. At h, the scalar variation identity and Ric(h)=3h give

\[
0=\operatorname{tr}_h Pu=R'_h(u)
=(\Delta_+-3)\operatorname{tr}_hu,
\qquad\Delta_+=-\Delta.
\]

The equality tr(Pu)=R′ includes the inverse-metric variation in R′; overlooking it would give the wrong scalar operator. Every background has Ric=3h. The Bochner argument gives the scalar spectral gap λ₁≥4: for Δ_+f=λf, integrate |Hess f|²+3|df|²=(Δf)² and use |Hess f|²≥(Δf)²/4 to obtain λ≥4 for nonconstants. Constants also fail (Δ_+−3)f=0. Thus tr u=0 and u is TT.

On TT tensors, the checked convention is

\[
2P=\nabla^*\nabla-2\mathring{\operatorname{Rm}}=-\Delta_L-6.
\]

For the unit sphere, the curvature action on a trace-free tensor is −u, so 2P=∇*∇+2 has no kernel. For CP², GV's least TT eigenvalue 32 is stated with Ric=6h; doubling the metric divides this by two. Hence −Δ_L≥16 and 2P≥10. On the equal sphere product, GV's factor-curvature-one metric has TT spectrum consisting of a simple zero and remaining eigenvalues ≥4. Multiplying its metric by 1/3 gives factor curvature 3 and multiplies this spectrum by three. Consequently 2P has eigenvalue −6 on the relative-scale tensor and remaining eigenvalues ≥6. In particular it has no zero eigenvalue. The product operator is invertible, not positive.

The product negative direction can also be checked directly: with h=h₁+h₂ and v=h₁−h₂, v is parallel and TT, \(\mathring{\operatorname{Rm}}v=3v\), so Pv=−3v. This agrees with the instability calculation and the spectral normalization.

R19 and compactness now imply

\[
\|u\|_{H^2}\le C\|Pu\|_2\quad\text{when }\delta_hu=0. \tag{R20}
\]

Indeed a contrary sequence normalized to H² norm one has Pu_j→0, a weak H² limit and a strong L² limit. The limit is a kernel tensor, hence zero. Applying R19 to the original sequence then contradicts its normalization. No positivity or dynamical stability is used.

In the C^{2,α} neighborhood R18, expansion of Ricci in background covariant derivatives yields a remainder Q with

\[
F(h+u)=Pu+Q(u),\qquad
\|Q(u)\|_2\le C\rho\|u\|_{H^2}. \tag{R21}
\]

The terms are smooth inverse-metric coefficients times u∇²u, ∇u∇u and background-curvature terms quadratic in u. Uniform positive definiteness and the C¹/C² smallness bound one factor by Cρ. This is not an H² algebra assertion in dimension four. Choose ρ after the fixed constant in R20, with Cρ small enough to absorb the remainder. Norm equivalence and diffeomorphism invariance give

\[
\|u\|_{H^2(h)}\le C\|F(h+u)\|_{L^2(h)}
\le C\|\operatorname{Ric}_k-3k\|_{L^2(k)}\le C\eta. \tag{R22}
\]

For the last step, Ric(k)−3k=L(τ) as a covariant tensor. A constant metric rescaling cancels exactly in the L² norm of a covariant two-tensor in dimension four, so R1 applies without a missing power of c.

There is no embedding H²→C⁰ in dimension four. Instead let m=‖u‖∞ and use the uniform background C¹ bound from R18. With a fixed Lipschitz bound K≥1, at a maximum point one has |u|≥m/2 on the h-ball of radius m/(2K), for m sufficiently small. Its volume is at least a fixed multiple of m⁴. Thus

\[
\|u\|_2^2\ge c m^6,
\qquad m\le C\eta^{1/3}. \tag{R23}
\]

The case m=0 is immediate. The tensor norm is Lipschitz by Kato; no global trivialization is needed for this argument. For m small, (1−m)h≤h+u≤(1+m)h, so lengths, distances and bounded model diameter give

\[
d_{GH}((M,k),(N,h))\le C\eta^{1/3}. \tag{R24}
\]

Combining R17 and R24 yields Cη^{1/8}=CD^{1/16}. If D=0, almost-Schur gives R=12 and hence Ric=3g; E0 applies directly and the distance to ℋ is zero. This avoids inserting η=0 into the logarithm or stopping time.

**8. Limiting order, alternative route and adversarial tests.**

The constants are fixed in this order: initial bounds; tail threshold and common T; τ=T/2 and the fixed-slice geometry; the Moser and distance constants; the two-metric packing constants; the three model elliptic constants and a small slice radius; finally a universal defect threshold meeting all these finitely many requirements and neighborhood entry. For each η>0, only the stopping time s=η² and spatial scale r=η^{1/4} vary. The spatial packing is complete before compactness is used to obtain the model neighborhood. Positive-time compactness supplies only neighborhood entry, with no required rate, because elliptic inversion supplies the rate inside that neighborhood.

The candidate's abandoned direct route is correctly delimited. Initial Bishop comparison and diameter/volume bounds give ball-volume lower bounds cr⁴. The segment inequality, Cauchy–Schwarz and ‖Ric−3g‖₂≤√5η give an averaged perturbed-endpoint segment error Cηr^{-4}. This does not reconstruct sectional curvature or controlled coordinates. The three distinct Einstein models themselves illustrate why trace control of Jacobi equations does not determine their full matrices. None of that route is used as an unproved interface in the affirmative proof.

The unequal-product family from I27 remains an adverse test. With unit factor metrics,

\[
g_z=a g_{S^2}+b g_{S^2},\quad
 a=[3(1+z)]^{-1},\quad b=[3(1-z)]^{-1},\quad |z|<1,
\]

one has R=12 and D=64π²z²/(1−z²). For |z|≤1/2, direct quadratic-form comparison with the equal product gives d_GH≤C|z|. The candidate's much weaker D^{1/16} rate is consistent with this. Volume-normalized flow obeys a′=a/b−1, b′=b/a−1, (ab)′=0, and (a−b)′=(a−b)(a+b)/(ab). The smaller factor decreases at least at its initially negative rate and collapses in finite time. This disproves attraction, not the proposed finite-time smoothing plus elliptic comparison. The retained negative mode in paragraph 7 confirms that no stability assumption has entered silently.

A second, genuinely smooth test checks the danger of converting small critical energy directly into a small pointwise initial defect. Let h be the unit round S⁴, choose a point p and a nonzero radial ψ∈C_c^∞(B_1(0)⊂R⁴) whose Euclidean trace-free Hessian is not identically zero. In normal coordinates set

\[
f_\ell(\exp_p(\ell y))=\alpha\ell^2\psi(y),\qquad
\widetilde g_\ell=e^{2f_\ell}h,
\]

extending by zero outside the coordinate ball. Here α>0 is fixed and sufficiently small, and ℓ↓0. Uniformly, |f_ℓ|≤Cαℓ², |df_ℓ|≤Cαℓ, |Hess f_ℓ|≤Cα. The exact conformal sectional formula gives sec(\(\widetilde g_\ell\))≥1−Cα after adjusting the harmless e^{-2f} factor, so choose α to make this positive for all small ℓ. This is a family of actual smooth simply connected closed positively curved metrics.

The exact trace-free Ricci formula is

\[
E_{\widetilde g_\ell}=-2\big(\nabla_h^2f_\ell-df_\ell\otimes df_\ell\big)^0_h.
\]

Conformal factors cancel in its four-dimensional L² energy. Rescaling the normal coordinates therefore gives

\[
D(\widetilde g_\ell)
=4\alpha^2\ell^4\int_{B_1}|(\nabla^2\psi)^0|^2dy+O_\alpha(\ell^6).
\]

The leading coefficient is positive. For radial ψ(y)=b(|y|²), the trace-free Hessian eigenvalues are (3,−1,−1,−1)|y|²b″, so an appropriate smooth cutoff b provides this explicitly. At an interior rescaled point where this tensor is nonzero, the initial defect has a nonzero limit of order α, although D→0. For a nonquadratic cutoff its derivatives can also grow as ℓ decreases.

Finally normalize by \(g_\ell=b_\ell\widetilde g_\ell\), where \(b_\ell=\overline R(\widetilde g_\ell)/12\). Integration of the conformal scalar formula gives

\[
\int R_{\widetilde g_\ell}\,d\mu_{\widetilde g_\ell}
=\int(12e^{2f_\ell}+6e^{2f_\ell}|df_\ell|^2)d\mu_h,
\]

so b_ℓ=1+O_α(ℓ⁶). This rescaling enforces average scalar 12, preserves positive sectional curvature and leaves D unchanged. Uniform metric comparison gives d_GH((S⁴,g_ℓ),(S⁴,h))≤C_αℓ², entirely compatible with the candidate estimate. This construction does not claim unbounded initial curvature; it rules out a vanishing pointwise-defect inference and tests concentration without inventing abstract nonrealizable curvature data.

Neither family exhibits slow GH convergence violating the theorem. Thin long spikes, collapse and small handles cannot be assumed to meet the hypotheses: the imported initial bounds and the proved two-metric argument obstruct those proposed failure modes. The universal-threshold issue has been resolved explicitly rather than tested numerically.

**9. Primary-proof comparison and limits of this verdict.**

I read the actual Tian–Wang [1202.2912v1](https://arxiv.org/abs/1202.2912v1) Theorem 3.1 assumptions and the distance proof through Lemma 4.4 and Theorem 4.1. Their local smoothing theorem assumes an initially almost Euclidean unit-ball volume as well as an initial Ricci lower bound. The present proof does not import that unverified almost-Euclidean initial lower bound. It uses EG's global smoothing, the initial Bishop upper coefficient and the fixed-time Euclidean lower coefficient instead.

Their Lemma 4.4 already subtracts the inner later-ball volume, excludes a large missing initial ball, finds a later-ball point near the initial endpoint, and packs disjoint later balls along an initial geodesic. Their Theorem 4.1 already uses fixed-time bounded geometry and subdivision to obtain a power distance estimate. The mathematical bridge here is a valid global application/adaptation of that method with R10 as the refined local volume budget. I have not called the packing mechanism novel.

If R10 were weakened to the all-subset global L¹ error |μ_k(U)−μ_g(U)|≤Cη, the hole budget would be r⁶+ar³+η. At r=η^{1/6}, R=O(η^{1/4}) and the all-pair error is η^{1/12}=D^{1/24}. Thus even a weaker power has a close antecedent. R10 improves the budget to the candidate exponent. Determining whether this improvement or the complete combination is substantial is specifically outside this round. No broader literature-absence assertion is made.

The current metadata retrievals confirm GV v2 (20 April 2013) and TW v1 (14 February 2012); the exact retained primary full texts, rather than metadata, supply the proof contracts. The author's two publisher HTTP 403 attempts remain recorded as failures, not read publications. I did not infer different theorem content from those failed requests.

Remaining mathematical objections under the stated premises: none identified. Remaining limits: corpus-relative truth; universal constants with a possibly ineffective entry threshold; no optimality; no dynamical attraction; significance undecided; no formal-machine or human-peer-review certification.

**10. Reproduction, provenance and scope.**

The parent record [i30-parent-verification.json](../experiments/i30-parent-verification.json) is retained unmodified in the review freeze. It reports 20,698 exact diagnostics, 11 frozen inputs, 34 pinned files, 17 primary retrievals, 7 contracts, 21 read passages and 57 sealed artifacts. These are exactly its stated reproduction counts, not mathematical acceptance. The parent later placed its preliminary note at [i30-parent-preliminary-review.md](../sources/i30-parent-preliminary-review.md), outside the sealed author directory; this path relocation is recorded separately in the review evidence. Its text was read both before and after relocation. It does not change the mathematical candidate.

The author reproduction scripts write derived outputs into their own directory. To honor this task's read-only requirement, [reproduce_author.py](../experiments/i30_einstein_metric_stability_r2/reproduce_author.py) executes their exact code with only the two output destinations redirected into the review directory, recording and asserting the literal substitutions. The author seal is checked in verify mode. All author counts above reproduce; only live shared-ledger drift is reported. The prior frozen ledger hash is `96eacd4b46a060066fc2255398dd0bedeb95a8eb2fc29c97b899e5af1ab53f94`; the live hash during this reproduction is `d4b67c3146c3f1c65822ecdb55d46bfa1ffd62749d51b479ce2f879c9d636927`. No mathematical-input drift is inferred from a changing shared ledger.

The independent diagnostics contain 4,759 exact cases covering the full-coordinate principal symbol, volume/normalization identities, Moser exponents, every subset in finite density evolutions, shell polynomial coefficients, logarithmic scale budgets, normalized products and the radial Hessian certificate. Their scope is finite/algebraic only; the universal proof is paragraphs 2–8. The first diagnostic implementation attempted to use an unavailable optional SymPy installation; it was replaced by a dependency-free rational implementation, without installing anything or writing outside scope. An initial evidence-build attempt encountered the parent's note relocation; the final builder uses the observed current path. Neither tooling issue is a mathematical repair.

From the project root, the reproducible review commands are:

```sh
python3 frontier/experiments/i30_einstein_metric_stability_r2/reproduce_author.py
python3 frontier/experiments/i30_einstein_metric_stability_r2/diagnostics.py
python3 frontier/experiments/i30_einstein_metric_stability_r2/verify.py
python3 frontier/experiments/i30_einstein_metric_stability_r2/seal.py --verify
```

The evidence builder performs snapshot/network operations and is not a retained-byte verification command. [The review input manifest](../sources/i30_einstein_metric_stability_r2/input-manifest.json) freezes 14 small control inputs. [The dependency manifest](../sources/i30_einstein_metric_stability_r2/dependency-manifest.json) records 103 reused read-only files; the actual 14 read passages are separately retained, with line ranges and fragment hashes. Two new versioned metadata responses have URL, date, status, size and SHA-256 in [new-primary-manifest.json](../sources/i30_einstein_metric_stability_r2/new-primary-manifest.json). The verifier distinguishes shared-ledger drift from immutable mathematical-input changes. The artifact seal covers this report and all designated review artifacts, excluding itself and derived verification output.

No shared index, author source, other project, staging area, commit or remote was changed by this review. No subagents were started. The PASS applies to the candidate as submitted; there is no repaired or weakened substitute theorem.
