# I303 — independent contribution review of full S302

2026-10-13. **Verdict: SUBSTANTIAL for the full frozen S302 package.** This is a contribution classification under the project's substantive-bridge standard, not an acceptance claim, a worldwide-priority certificate, or a complete proof PASS. I298's TECHNICAL verdict remains unchanged for its frozen restricted S295 target. The change in assessment comes from I300's all-amplitude entropy/translation compatibility estimate, not from renaming the older chain.

All OpenAI theorems and operative inequalities at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Every I128/I131/I290/I295/I300 deduction remains internal. I read their actual needed proofs and the finalized I298 package. After the user's supplemental authorization, I also read the finalized I301 package: its PASS unchanged covers U300, the non-strict Gaussian interface, and the rearrangement/compactness implication G290. It expressly excludes the complete older cube chain. After a second explicit finalization authorization, I read and authenticated the finalized I299 package as well. It passes the complete restricted S295 chain, including actual old bridge proofs, and supplies no unrestricted-S302 or contribution verdict. Neither sibling was read while live.

## 1. Exact theorem classified and proof boundary

Let X be uniform on {-1,1}^n, n>=1, and let T_r be independent bit noise of correlation r. Define

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=E psi(u)-psi(Eu),
    d_a(u)=min_(i,epsilon=±1) E|u-epsilon*a*X_i|^2,
    Delta_r(u)=psi(ra)-I(T_r u).

For every 0<a0<=a1<1 and 0<r0<=r1<1, S302 asserts existence of C=C(a0,a1,r0,r1)<infinity such that

    I(u)=psi(a), a in [a0,a1], r in [r0,r1]
        => d_a(u)<=C Delta_r(u)

for every finite n and every u:{-1,1}^n->[-1,1]. There is no restriction on r1*a1, bias, endpoint values, support, initial closeness, singleton size, phase, rank, or complexity. C is existential and independent of n. Constants need not remain bounded as an endpoint approaches 0 or 1. Restricted S295 and full S302 are one target and cannot be counted separately.

The frozen S302 analysis matches `1db6cef312fa1e705c150b1bc2c1ea0484d50915278f602f579074e3dbab6cf8`. Its report and authentication were read. The I300/I290/I295 and I298 report/analysis hashes supplied in the brief match. The supplemental I301 report/analysis hashes match as well. Exact byte and passage records are in [input-authentication.json](input-authentication.json).

No contribution-blocking mathematical gap was found in the operative chain or in the new comparison. This finding is a scoped assessment, not a replacement for the full independent proof audit. In particular, I301’s finalized U300 PASS is not a PASS for the old cube bridges or the full theorem. I299 now separately passes the old deductions needed for restricted S295; neither final report issues a full S302 PASS.

## 2. The constructive old-method reduction really does cover the older package

I agree with I298's concrete classification of the frozen restricted result. It did not claim that Boolean stability alone suffices or that the entire soft theorem is duplicated in print. The following operations account for the complete old contribution package; they are not discarded as earlier accepted results.

**Compression.** Sort coordinate fibers increasingly, preserving the full input law, mean, second moment M=Eu^2, and information. At the decisive fiber write b+X_i d. If c is the final singleton and b_i is the original one, Ed=b_i, E|d|=c, and Ed^2<=M. Strong convexity of the even noisy entropy function and the nonconstant spectral bound give

    (1-r^2)(c^2-b_i^2)<=2 L_gain/r^2+r^2(M-c^2).

Since d_a(g)>=M-c^2 and d_a(g)>=(a-c)^2, this yields Q131b,

    d_a(u)<=C_comp[d_a(g)+L_gain],
    Delta(u)=Delta(g)+L_gain.

The soft adaptation replaces the Boolean derivative identity with the actual second-moment inequality. The underlying quantitative sorting calculation is already in [Ky–Tran stability, Lemma 3.3](https://arxiv.org/html/2609.31797v1).

**Local linear coercivity, including spikes.** At v=aX_1, the constrained entropy functional has zero first variation and Hessian

    Q(h)=k[Eh^2/(1-a^2)-(Eh)^2]
            -[E(T_r h)^2/(1-r^2 a^2)-(Eh)^2],
    k=r atanh(ra)/atanh(a).

Every nonconstant Walsh coefficient is at least q_H=k/(1-a^2)-r^2/(1-r^2a^2)>0; the constant coefficient is a^2 q_H. The elementary monotonicity of (1-t^2)atanh(t)/t pays positivity uniformly on each compact rectangle. Splitting h into small amplitude and small support pieces, real-function hypercontractivity makes the noisy support tail negligible compared with its input quadratic energy. An output remainder of order ||h||_2^p, p>2, is absorbed. This is the actual L131 argument, including endpoints and arbitrary mean, not an L-infinity surrogate. [Yu's Lemma 4.4 and local discussion](https://arxiv.org/html/2410.10147v5) and Ky–Tran's local estimate supply the methodological comparisons, not an unchanged soft theorem.

**Marked joining and global entrance.** The pinned canonical optimizer is already unique. Retain the strict common-corner margins in `reserve:corner-margin` and `thinning:derivative-loss/window-bound`: with c0=2-4(log 2)^2>0, a corner ray loses at least a constant times retention*(1-retention)*separation^2. Composing the two retentions gives (c0/8)(1-k_core)delta^2. Equality at a nonzero face-mean separation therefore excludes corner mass. The deterministic capacity step is strict at nonzero center because H(m)-(1-m^2)log2>0. Strict-F parents lose by thinning or the one-corner wall comparison. Unique optimality then identifies the actual equality pair law as a deterministic reflected pair. These are retained source losses, rather than a newly solved optimizer problem.

Pair laws live on one fixed compact square. A cost sublevel and separation lower bound give a compact physical set; lower semicontinuity and that equality classification yield a qualitative marked modulus. The exact source energy split makes production surplus dominate joining loss. Thus P290 provides entrance at a specified nonzero singleton with arbitrary remaining dimension.

The I128 integrating factor is

    z'=R-Az, 2<=A<=K,
    z(s)<=exp(K t_max) Delta,
    integral_0^t R(s)ds<=exp(K t_max) Delta,
    t=-log r, t_max=-log r0.

It selects a middle positive time with small surplus; a marked singleton remains at least r0*beta. Original-budget strong convexity pays the return to u: the squared original distance is bounded by C sqrt(q)+Cq when q is the smoothed squared distance. This only gives entrance; applying L131 at the original kernel supplies the final linear rate. Larger deficits are paid by d_a<=4. Hence B290 applies globally whenever max_i|uhat(i)|>=beta, with no closeness, balance, or remaining-coordinate bound.

**Old diffuse sector.** Borell/layer cake/convex order give a scalar monotone rearrangement preserving the entire law. Scalar conditional EPI applied separately to both biased posteriors gives

    B_r(J)=-0.5 log(1-r^2+r^2 exp(-2J)).

The I295 curvature/chord calculation pays an absolute gap below the cube curve for the small-amplitude region. An unequal fixed noise split and fixed-degree invariance transfer both information budgets, with clipping and mean terms paid. This closes S295 when r1*a1<1/sqrt(2). Each operation above has the original all-n, arbitrary-soft scope required at its interface. I298 therefore left a genuine all-amplitude strictness obligation, not an unacknowledged soft-kernel gap in its restricted reduction.

## 3. What the new unrestricted mechanism adds

Write f_r(J)=psi(r psi^{-1}(J)). The non-strict Gaussian inequality follows internally from the stipulated cube theorem by conditional block-sum replacement: conditional on every output bit configuration, centered input summands have the same variance and a uniform O(M^(-1/2)) smooth-test replacement error. This transports posterior means and then entropy. Ordinary joint weak convergence alone would not suffice. OU smoothing and bounded entropy continuity extend the result to all measurable scalar kernels. I301 independently checks this interface.

Suppose a positively smoothed nonconstant scalar w attained equality. The nonnegative functional

    G(v)=f_r(I(v))-I(Q_r v)

would attain its global minimum zero at w. Compact additive perturbations give the Euler equation

    Q_r atanh(Q_r w)=k atanh(w)+(1-k)atanh(m),
    k=f_r'(I(w)), m=Ew.

There is no free mean or information multiplier: perturbations vary both, and G already includes their comparison. Differentiating this identity spatially and using self-adjointness gives the weighted derivative identity

    E[(Q_r w')^2/(1-(Q_r w)^2)]=k D/r^2,
    D=E[w'^2/(1-w^2)]>0.

Translations w_h(x)=w(x+h) are admissible for both signs. The Euler equation cancels the acceleration term in their second variation, leaving

    G''(0)=kD+f_r''(I) A^2-kD/r^2
                    +(1-k)(Ew')^2/(1-m^2),
    A=E[(atanh(w)-atanh(m))w'].

The output parameter derivative is Q_r w', not the spatial derivative r Q_r w'. That distinction supplies the factor r^(-2). Since f_r''<0, Cauchy–Schwarz implies

    G''(0)<=D[k(1-r^(-2))+(1-k)(1-q)],
    q=Var(w)/(1-m^2).

This is where an unqualified appeal to a familiar translation argument stops. The last, positive mean term remains even in dimension one. Setting it to zero would narrow the target and would generally fail even for a balanced increasing w: its translation need not preserve its mean.

The biased binary joint-likelihood calculation gives I(w)<=log(1+q), so q>=b=exp(I(w))-1. This Jensen/Renyi operation is old. What closes the sign, at every amplitude and correlation, is the particular nonlinear comparison

    k=r atanh(ra)/atanh(a)
       >r^2(1-b)/(1-r^2 b), b=exp(psi(a))-1.       (S)

It makes the entire second variation strictly negative. Neither generic concavity (which here gives only 0<k<r^2), nor ordinary Gaussian LSI nonattainment, nor a fixed-mean translation test pays (S).

The displayed proof of (S) has two concrete parts. Set

    M(a)=[a/(1-a^2)-atanh(a)]/[a/(1-a^2)+atanh(a)].

First, b>M(a). Its equivalent K(a)>0 has K(0)=K(1)=0 and derivative numerator 1-t coth(t)+t^2 sech(t)^2, a=tanh(t). The classical coth expansion makes the ratio (t coth(t)-1)/(t^2 sech(t)^2) strictly increase from 1/3 to infinity, proving exactly one sign change and positivity of K. Second, M(z)/z^2 increases by positive coefficient pairing. For F(x)=atanh(a sqrt(x))/(a sqrt(x)),

    F'/(F+xF')=M(a sqrt(x))/x<=M(a)<b.

Thus (1-bx)F(x) strictly decreases; its comparison between r^2 and 1 is exactly (S). The two pieces match the entropy exponential, the curve slope, and the biased variance reserve. The NIST product/partial fraction and the coefficient-ratio technique are classical; the contribution lies in this compatibility estimate and its use to exclude every positive-information equality kernel.

Prior smoothing supplies quadratic bounds for atanh(w), bounded ordinary derivatives, and the pointwise Fisher bound w'^2/(1-w^2)<=tau^2/(1-tau^2). The tilted-Gaussian entropy/mean estimate bounds (atanh(w))' linearly in |x|. These are integrability payments, not a new tail hypothesis. The semigroup identity f_s composed with f_tau=f_(s tau), together with monotonicity, transfers any putative nonsmooth equality to a positively smoothed equality. No analytic continuation or extra LSI reserve is imported. My independent sign and interface checks agree with finalized I301; its detailed output-domination arguments justify the frozen claims without changing them.

## 4. Concrete closest-predecessor comparison

A stronger comparison than simply calling translations old is available. [Heilman–Tarter, current v2](https://arxiv.org/pdf/2011.05583v2), Lemma 5.1 and equations (9)–(11), differentiate a stationary Gaussian noise-stable set and obtain an almost-eigenfunction identity for translations. A volume-preserving translation has a second variation with a favorable factor 1/r-1. Rank-nullity then reduces a partition optimizer to a lower-dimensional set. Their proof really does precede the general strategy of using translation instability to constrain Gaussian optimizers.

That mechanism is not an all-amplitude standard-result reduction of S302. Its functional is quadratic set noise stability; its constraint is prescribed Gaussian volume. In one dimension the required volume-preserving translation direction can be absent, and the theorem leaves a one-dimensional optimizer rather than excluding all positive-information soft kernels. I300's functional is a nonlinear information-curve deficit. Its translation varies both the input information and mean, produces the positive mean term above, and needs (S) to pay that term. The classical commutation calculation itself is not the substantive new item; its compatibility with the binary entropy curve and arbitrary bias is.

[Heilman's variational robust-noise-stability manuscript](https://www.stevenheilman.org/~heilman/papers/robustone.pdf), Theorem 1.6 and its translation/penalty discussion, makes the comparison closer still: a penalty term can be carried through a translation argument. But its inspected bound is for sets, fixed Gaussian measure, a centroid lower bound, and the displayed geometric penalty. It neither substitutes f_r(I(w)) for that penalty nor supplies (S). Thus I300 should credit that precedent and avoid claiming that variational perturbation of a Gaussian objective is new.

The other primary comparisons have equally concrete scope differences:

- [Kindler–O'Donnell–Witmer v3](https://arxiv.org/pdf/1506.03167v3), Theorem 3.1, optimizes Boolean Gaussian outputs at a fixed mean. It does not fix actual positive soft information while preserving arbitrary input laws. Replacing a soft kernel by a set changes E psi(w), so this theorem does not supply the required strictness.
- [Chechik–Globerson–Tishby–Weiss](https://jmlr.org/papers/volume6/chechik05a/chechik05a.pdf), Sections 2–5 and Theorem 3.1, analyze continuous Gaussian representations and their information curve. Scalarizing their curve gives the EPI comparator B_r, not f_r. Restricting the representation to a binary sign gives an inequality below B_r; it does not compare its reserve with B_r-f_r.
- [Polyanskiy–Wu current v4](https://arxiv.org/pdf/1508.06025v4), Theorem 4 and Section 2.2, formalize fixed-input and nonlinear SDPIs. [Calmon–Polyanskiy–Wu current v2](https://arxiv.org/pdf/1512.06429v2), Proposition 2, gives the BSC curve, while its AWGN Theorems 1/3 give strict loss from the identity/capacity curves under power constraints. The BSC curve coincides with the cube comparator in the one-bit setting, but an AWGN channel is not a BSC. Strict loss from J or from Gaussian capacity supplies no comparison with the smaller f_r(J).
- [FIL](https://www.normalesup.org/~mfathi/docs/LSI14.pdf), Theorem 1/Corollary 2 and the full OU proof, require posterior Poincare information. [ELS v2](https://arxiv.org/pdf/1903.04522v2), Corollary 2/Theorem 3, require the indicated individual second-moment/covariance conditions for the stronger conclusions. Complementary posteriors supply pooled moments, not those separate hypotheses. Moreover their ordinary LSI deficit is D_G-2I, whereas the required reserve is above F(I)-2I. I300 circumvents that optimization; it does not solve it by assuming an unspecified stability theorem.

The EPI obstruction is analytic, not a scan or a source-absence claim. For H(x)=exp(-2psi(sqrt(x))), H'(x)->-infinity as x approaches 1. For x sufficiently close to 1, the chord discrepancy

    g_x(theta)=1-theta+theta H(x)-H(theta x)

has g_x(1)=0 and g_x'(1)=H(x)-1-xH'(x)>0. Hence g_x(theta)<0 for theta just below 1, i.e. B_r(psi(a))>psi(ra) at some open high-amplitude parameters. Strict EPI alone leaves an unmeasured reserve. The new exclusion treats exactly that region as well as the earlier one.

## 5. Why the new estimate reaches the full global linear theorem

The resulting scalar strictness applies to every 0<I<log2 and every 0<r<1. Borell rearrangement and scalar monotone compactness turn it into G302: a positive absolute Gaussian gap uniform over every compact open amplitude/correlation rectangle and every finite Gaussian dimension. Compactness is in the fixed scalar class; growing Gaussian spaces are never declared compact. These are old I295 operations, separately checked by I301.

On any original S302 rectangle choose r1<lambda<1. Both lambda*a and sigma=r/lambda range in compact open intervals; no upper bound lambda*a<1/sqrt(2) is needed. The integrating factor pays the input and output budgets of h=T_lambda g. For a diffuse increasing sequence, a fixed degree-d truncation has spectral tail at most lambda^(2(d+1)), and its actual L2 influences are at most lambda max_i ghat(i). The primary [MOO Theorem 3.18, Hypothesis 4](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n1-p05-p.pdf) gives the fixed-degree replacement bound; clipping and bounded entropy continuity pay both budgets and means. Define b=psi^{-1}(I_G(v)) exactly. G302 then contradicts a sequence of vanishing deficits and singletons, with degree chosen before the sequence limit.

Therefore some beta,eta>0, depending only on the four endpoints, give an absolute deficit eta throughout the diffuse increasing sector. There d_a<=4 gives d_a<=4 Delta/eta. B290 supplies C_beta Delta in its complementary marked sector, and Q131b returns to arbitrary u. A valid final constant has the form

    C=C_comp max{1,C_beta,4/eta}.

Thus the linear rate still comes from the older local/marked machinery; I300 supplies the missing all-amplitude global entrance obstruction. The result is not only pointwise Gaussian nonattainment, a fixed-dimensional estimate, or an improved parameter threshold with another hidden restriction. It removes the entire diffuse obstruction on every allowed rectangle and yields the exact full all-n linear theorem, through the older internal proofs at their actual stated scopes. Their use has now received supplemental restricted-chain proof evidence from finalized I299; unrestricted S302 remains outside both sibling reports’ certified theorem scope.

## 6. Decisive judgment, attribution, and limits

**SUBSTANTIAL.** Under the stated standard, the new bridge is the entropy-specific translation instability estimate (weighted derivative identity plus biased likelihood reserve plus the all-amplitude slope comparison (S)), and the structural consequence is exclusion of every diffuse Gaussian near-extremizer uniformly on all compact open parameter rectangles. Its completion of the global all-n arbitrary-soft linear stability theorem is a material mathematical scope extension beyond I298's old-method reduction.

This decision does not elevate quantitative sorting, local Hessian coercivity, marked optimizer margins, compactness, invariance, Jensen/Renyi, or classical hyperbolic identities into new findings. Translations and their almost-eigenfunction role have a concrete primary predecessor. The substantive addition is the particular nonlinear compatibility that makes the residual bias term have the correct strict sign throughout the previously unpaid high-amplitude region. Elementary proof ingredients and proof length do not dispose of that additional estimate.

The checked sources do not furnish a constructive standard-result reduction paying that estimate at the same quantifiers. This is evidence for the operation-level contribution judgment, not a proof of absence from all literature. Worldwide priority, optimality of the Gaussian bound, effective C, sharp dependence near parameter endpoints, and authorship-level priority are not established. I300 is parent-authored; I303 assesses rather than claims its discovery. I298 stays TECHNICAL for S295, one full-theorem nomination replaces the restricted form, and the user-supplied count thirteen toward twenty is unchanged.

Proof and contribution gates remain distinct. Finalized I301 passes the new Gaussian mechanism and its gap consequence unchanged. Finalized I299 passes the complete restricted S295 chain, including the actual older deduction proofs. These are complementary, scoped proof records; neither certifies unrestricted S302, and I303 does not issue that separate full-proof verdict. This review authorizes no acceptance, count update, staging, commit, or publication.
