# Weighted logarithmic Brunn–Minkowski equality: prefreeze derivation

PREFREEZE / no nominee. These are feasibility calculations and a conditional closure analysis, not a frozen theorem, full author proof, correctness grade, contribution grade, or acceptance. The pinned Source091 and its operative proofs are stipulated true. No truth audit of them is attempted.

## 1. The full question explored

The question is equality in the source's logarithmic Brunn–Minkowski inequality for **arbitrary even log-concave Radon measures** and arbitrary origin-symmetric convex bodies, including measures on proper subspaces and densities with finite support or infinite boundary potential. A smooth, everywhere-positive, uniformly convex, Gaussian, fixed-facet, or fixed-product restriction is not a replacement answer.

For the exploratory calculation, discard the trivial zero measure and point-mass cases, and work in the linear span E of the support. Let S be its closed convex support and write dµ=e^{-V}dx_E, with V even convex and extended-valued. Normalization is immaterial on the bounded sets in question. Let K,L be the original ambient bodies, let A=K∩S, B=L∩S, and let

    D_t = W_ambient[h_K^(1-t) h_L^t],
    C_t = W_E[h_A^(1-t) h_B^t],      0<t<1.

A and B are relative full-dimensional bodies containing zero in their relative interiors. The source's support-subspace argument and the ordinary Wulff intersection comparison give

    C_t ⊂ D_t∩S,
    µ(D_t) ≥ µ(C_t) ≥ µ(A)^(1-t) µ(B)^t.                 (1)

Thus original equality requires equality for the clipped pair and zero µ-mass in the inclusion difference. Ignoring this clipping gives a false statement: any two different symmetric bodies containing a small uniform-density support have the same full mass, and their interpolation also contains that support. Their geometry outside S is unobservable.

The prospective geometric description involves complementary product factors of A and B, the same undilated factor in the directions where the density varies, dilation only in density-flat directions, and saturation of (1). This is not a frozen assertion or a literature-open designation. No full necessity theorem is claimed here.

## 2. Actual old operations that cannot be recounted

I43's original §§2–6 supplies the concavity/first-variation reduction to normalized cone-volume data, the Gaussian determinant/matroid mechanism, retained source defects, and the precise warning about redundant slabs in the hard limit. Its full unrestricted volume-equality target is unchanged. In particular finite soft-slab equality or generic nonresonant polytopes would be weaker substitutes, not candidates.

I49's actual full original proof was read. It supplies the finite-defect hard fields, retained regularizer and derivative energy, local Sobolev compactness, signed contact-pair boundary identity, radial BV passage to normal tests, core/tail estimates, compatible product-image construction, and two-endpoint reconstruction with the mean score retained. Its hypothesis scope is the uniform/Gaussian-regularized hard-target construction used for its volume statement. Its operations are credited; the present note does not reopen its statement or assign it a fresh grade. Related I44–I48 originals were not recovered through protected filename categories; the broad *log* rule omits genuine relevant mathematics. I49's account of those papers is not a substitute claim of having read them.

The source's measure consequence already handles all even log-concave Radon measures, including lower-dimensional support. Saroglou's actual Section3 proof also pays the plateau/truncation, vertical shift, geometric level interpolation, multiplicative Prékopa–Leindler, and approximation operations. Reproving measure log-concavity, independent slab-width concavity, or mixed-homogeneity variance by these operations would not supply a new substantial operation.

## 3. Retain the background curvature in the strongest source completion

First take a smooth even convex background V0 and put

    Ψ = V0 + ε|x|²/2 + Σ_i ψ_i,
    ψ_i(x) = |p_i·x/h_i|^q,
    h_i(t)=h_i(0)e^(t b_i),
    F = -q Σ_i b_i ψ_i,        U=F-EF,
    dµ_soft = Z^(-1)e^(-Ψ)dx,
    dν=e^(-φ)dz, x=∇φ, τ=D²φ, M=τ^(-1).

Here ε>0 and q is an even integer. For a compact even source test in the source's target-coordinate notation,

    P=τ D_x²v, B=Pτ, W=δ_µ B=P x-div_z P,
    u=δ_µ W, R=D_zW-B, H0=D²V0, Hi=D²ψ_i.

The source tensor computation is valid for this background: its compact integrations do not require that all of Ψ be homogeneous. Homogeneity is used separately on each ψ_i. The complete LSX square completion (actual equations3.10–3.16, read in context) consequently gives, with

    D = q² Σ_i b_i² Eψ_i - Var(F) = -(log Z)'',

    D + ||u-U||²
      = T(v) + ε E[tr(MB²)+|W|²]
        + E[tr(MB H0 B)+WᵀH0W]
        + Σ_i E tr(M(B+b_iτ)Hi(B+b_iτ))
        + Σ_i E (W+b_i x)ᵀHi(W+b_i x).                (2)

All right-hand terms are nonnegative. In particular

    T(v) ≥ E||M^(1/2) R M^(1/2)||² + (1/2)E 𝒟(P),
    𝒟(P)=M_ab τ_kr M_ls (∂_l P_ak)(∂_s P_br).         (3)

The source's two tensor squares equal one half of the full derivative square plus three halves of its symmetric part in a constant normalized frame. A variable frame is not differentiated. This stronger derivative control must not be discarded.

For clarity, the elementary completion uses m_i=Etr(τHi)=qEψ_i, d_i=Euψ_i, and γ_i=-b_i. The two summand squares expand to

    Etr(MBHiB)+EWᵀHiW - 2qγ_i d_i + q²γ_i² Eψ_i.

Their sum, the background terms, and the weighted Bochner identity give D+||u-U||². Evenness removes the linear projection; it does not remove the mean EF. The Gaussian coefficient ε supplies the global W bound.

The same algebra works for individually homogeneous smooth convex summands of degrees q_i>1 with F=-Σq_i b_iψ_i and γ_i=-b_i; this is a routine modification, not a nominee. Neither this calculation nor a positive-curvature special case is offered in place of the full weighted question.

## 4. Compatible regularization and hard compactness

If equality holds for the clipped pair, t↦logµ(C_t) is affine. Write its slope s=logµ(B)-logµ(A). On bounded bodies, adding ε|x|²/2 changes a log integral by at most εR²/2. A smooth even convex approximation of V can be chosen with integral errors as small as a prescribed positive budget on a common enclosing ball. Since all C_t contain a common relative ball with positive µ-mass, this controls the log errors uniformly in t.

The source/LSX order is essential: select the approximation and direction net, then q sufficiently large for the partition error and N q^k ρ^(q-k) interior errors, then the source dense test. Choosing the Gaussian regularizer comparable to the total artificial error budget d gives, at a time in [1/3,2/3],

    D ≤ C d,       EF = -s + O(d),
    E𝒟(P) + E||M^(1/2)RM^(1/2)||² ≤ C d,
    E|W|² ≤ C.                                          (4)

A zero-mean score is not a zero mean **F**. The constant mean in the final flux is m=-s.

The soft cap 4/ε is not a radius-only cap. The useful stronger route is to take a hard target at a fixed smooth background/regularizer first. Klartag1309.2767v1 Theorem1.1 gives trD²φ≤2R² for a bounded target under its stated smooth bounded-potential assumptions. Its complete Section5 cap proof, including the final removal of boundary/strict-convexity assumptions, was read. That theorem does not literally state the entire nonsmooth extended-valued version needed here. Its approximation argument, however, is a compatible route and must be credited, not ignored.

Here is why that route goes substantially beyond a failed 4/ε estimate. For smooth hard targets with radius bounded by R and densities uniformly bounded above and uniformly positive on an inner ball, the source supporting-plane calculation gives uniform coercivity and bounded minimum normalization. The cap gives uniform C^(1,1) control. The moment equation

    detD²φ_j = Z_j exp[-φ_j+V_j(∇φ_j)]

and a uniform lower bound on V_j give a positive local determinant lower bound. Together with the cap this gives local positive lower eigenvalue bounds. Thus one can seek C¹ convergence to a strictly convex limiting moment map, identify its gradient image using pushforward and supporting planes, and then use local Lipschitz convergence of the convex potentials on the interior to obtain C²,α estimates. Only after the image is known to stay in a common interior compact can those local target bounds be used. Stating that order matters; smooth convergence on the whole closed support has not been assumed.

With those compatible coefficients available, (3)–(4) give exactly the primary/I49 compactness mechanism: P is locally close to its average, W is locally close to that average times ∇φ, and the inner-ball Gram matrix bounds the averages. A subsequence gives a single constant matrix Q with

    P_j → Q,    W_j → Q∇φ locally,
    QD²φ = D²φ Qᵀ.                                     (5)

There is no need to invent an inverse of the hard moment operator. I49's ordinary Neumann inverse does not enforce (5), and its one-dimensional boundary-load obstruction remains valid.

This section is an integrated feasibility route, not a completed theorem with every approximation and domain assertion proved. The stronger cap and the existing field construction make bare 'loss of ellipticity' an inadequate explanation of what is unfinished.

## 5. The signed boundary quantity is better than an unsigned boundary measure

For a smooth approximant, split powers into one-sided powers when attaching their normals and set

    Λ_j(dx,du)=Σ_i q_j ψ_ij(x) µ_j(dx) δ_(p_ij)(du).

Even convex V_j satisfies x·∇V_j≥0 after subtracting its minimum. Radial integration therefore gives

    Λ_j(1)=n-ε_j E|x|²-E[x·∇V_j] ≤ n,
    Λ_j(|x|²)=(n+2)E|x|²-ε_j E|x|⁴
                  -E[|x|² x·∇V_j] ≤ (n+2)E|x|².       (6)

These are the strongest elementary bounds: the extra potential term has a useful sign. Thus total layer mass and tightness are not missing merely because ∇V can become large.

The source contact argument still places all limits on active pairs

    x∈∂C_t,    x·u=h_Ct(u)=h_A(u)^(1-t)h_B(u)^t.

At a regular boundary point also on ∂S, a supporting normal of S is the unique normal of C_t. Since A,B⊂S, contact implies

    h_A(u) ≤ h_S(u), h_B(u) ≤ h_S(u),
    h_Ct(u)=h_S(u), hence h_A(u)=h_B(u)=h_S(u).

In particular b(u)=log(h_B/h_A)=0 there. This observation addresses a real complication: background gradients may concentrate on a common support boundary, and the unsigned layer measure need not have a unique naive split into 'body boundary' and 'density boundary' parts. The signed measure b(u)Λ_j can still have a well-defined limit, because its multiplier vanishes on that ambiguous part and (6) bounds its total mass.

On boundary portions compactly inside intS, V is finite and locally Lipschitz. The intended local passage is the ordinary weighted divergence theorem, with density e^{-V} and the source's unique-normal contact argument. Together with the vanishing multiplier at ∂S, the desired global identity is

    ∫_C Qx·∇g dν_C
      = -∫_(∂C∩intS) g b(ν_C) h_C(ν_C) ρ_C dH^(d-1)
        -m∫_C g dν_C,                                  (7)

where ν_C=µ|C/µ(C), ρ_C is its interior density, and m=-s. A zero trace on part of ∂S must not be replaced by a positive lower bound.

Local W convergence plus the global L² bound in (4) pays crossing a thin target boundary layer, as in the actual primary proof. What has not been supplied here is one end-to-end lemma constructing all approximants and proving (5) and (7) simultaneously for every extended-valued V, including the density trace at a moving contact with ∂S. The vanishing-multiplier argument and bounds (6) are positive progress toward that lemma; they are not a counterexample to it or a certificate that it is a nonroutine new operation.

## 6. Conditional density rigidity: do not leave elementary algebra unpaid

Assume the compatible moment map, constant Q, and global flux identity have been obtained. A constant dual coordinate change makes Q symmetric. The commutation in (5) then annihilates mixed Hessian blocks between distinct eigenspaces. On the whole source space, integration gives

    φ(z)=constant+Σ_i φ_i(z_i),
    C=⊕_i C_i,

and the pushforward product structure makes the restricted target density a product. This is the primary proof's global product mechanism, not merely simultaneous diagonalization at one point.

For a smooth finite background, the retained H0 term in (2) also gives

    D²V(x) Qx=0.

Along the radial segment tx, evenness gives ∇V(0)=0 and hence

    ∇V(x)·Qx = ∫_0^1 xᵀD²V(tx)Qx dt=0.

Differentiating and using the previous vector identity yields Qᵀ∇V=0. Thus V is independent of each nonzero-eigenvalue block. This argument allows opposite signs among the eigenvalues; an unjustified common contracting-flow direction is unnecessary.

There is a stronger conditional route that avoids taking a limit of the Hessian measure of V. For tests compactly inside C, (7) says

    div(ρ_C Qx)=m ρ_C,
    Qx·∇V=trQ-m                                          (a.e.).

Local Lipschitz boundedness near zero forces the constant on the right to be zero, so trQ=m. The product density from (5) writes V=constant+Σ_i V_i(x_i) in the interior. Varying one factor at a time gives

    a_i x_i·∇V_i(x_i)=0.

For a_i≠0, absolute continuity on radial intervals implies V_i is constant. This avoids a fictitious positive curvature lower bound and avoids treating the Hessian of a nonsmooth V as an ordinary matrix-valued function. The undilated zero-eigenvalue factor may carry an arbitrary even convex potential.

## 7. Conditional endpoint recovery by saturation, including vanishing density

This is a further compatible reduction, not an additional gap. Suppose the preceding product structure and signed flux are valid. On positive-density product faces the flux gives b(u)=-a_i for normals in the i-th block. On a zero-density face, a nonzero-eigenvalue block would have constant positive factor density and the other coordinates are interior almost everywhere, so its interior trace would be positive. Thus zero-density faces belong to the zero block. On ∂S the zero signed term in (7), compared with the trace of ρ_C Qx, handles positive-density jumps as well. These distinctions are necessary; positivity of all weighted surface masses is false in general.

The contact relation then suggests the comparison bodies

    A#=e^(tQ) C,       B#=e^(-(1-t)Q) C.               (8)

Supports on the full product normal support give A⊂A#, B⊂B#. Support data there alone need not give equality: cutting a corner can preserve some support values. The missing endpoint argument is supplied by mass, not by silently assuming a common normal fan.

Write x=x0+x' according to the zero block and its complement. Inside C the density has the form e^{-V0(x0)}, independent of x'. Convexity supplies the global lower bound

    V(x0+x') ≥ V0(x0)                                  (9)

for x0 in the interior of C0. Indeed, at (x0,0), a supporting subgradient of V has no component in the flat directions; its supporting inequality at points with the same x0 gives (9). The maps in (8) fix x0. Consequently

    µ(A#) ≤ e^(t trQ) µ(C),
    µ(B#) ≤ e^(-(1-t)trQ) µ(C).

Since trQ=m=-s and logµ(C)=logµ(A)+ts, the right sides are exactly µ(A),µ(B). Together with inclusion, these inequalities must saturate. Saturation would force both the endpoint bodies and their density-flat extensions to match: the reference density on A#,B# is positive in their interiors, so a proper convex cut or a positive-volume density decrease would make the inequality strict. Convexity then propagates density flatness to the convex hull of the two endpoint products. This rules out the tempting but incorrect assertion that one must separately assume flatness beyond the intermediate body.

Thus, once the joint hard-limit/trace statement is established, a large part of 'global reconstruction' is already paid. It would be misleading to leave all endpoint or density reconstruction as a black-box nonroutine obstacle.

## 8. Stronger primary comparison and actual outcome

The current primary Sharp stability for the (B)-theorem,2608.08472v1, was read through its functional statement, regularization, even Poincaré proof, complete strong covariance proof, and complete improvement in the large-variance regime. It already obtains a universal covariance remainder for even 1-log-concave measures, including functional rather than indicator inputs. Its Bochner/inverse/stability and singular-value-selection operations are credited. They are not full arbitrary-background weighted Wulff equality, but they prohibit treating smooth Gaussian/positive-floor support or covariance dichotomy as a fresh contribution. HLRV2305.17794v1 was acquired; its original proof body was not freshly read, so the later manuscript's account is not mislabelled as a complete original/transitive read.

The completed source/primary/project composition pays (2)–(6) in their stated smooth or conditional settings and the conditional algebra and saturation in §§6–7. The remaining author obligation is an actual full-scope, simultaneous approximation/compactness/signed-trace proof supplying (5) and (7), followed by explicit treatment of the support-subspace and inclusion saturation in (1). Several concrete routes have been identified; no failure of a naive ellipticity estimate or level-set transfer proves that the full operation is impossible.

No demonstrably new nonroutine operation beyond the strongest integrated construction was established in this round. There is also no complete unrestricted theorem or independently grounded new-to-literature claim. These reasons support PREFREEZE/no nominee; they are not an independent contribution verdict. No smooth-background substitute, finite-soft equality classification, fixed-product assumption, Gaussian covariance corollary, or renamed I43/H49 result is submitted. All frozen old scopes, including the user-listed protected targets, remain unchanged.
