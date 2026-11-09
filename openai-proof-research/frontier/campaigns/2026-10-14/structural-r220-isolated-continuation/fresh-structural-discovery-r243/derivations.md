# r243 working mathematics — PREFREEZE

No statement or proof scope has been frozen. No grades or count are assigned. Source368 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and all its operative proofs are stipulated true.

## Source low-exponent construction, first semantic pass

The pending-reading language in this chronological first-pass entry records its original timing. Both complete source constructions and the figures were subsequently read before the completed reductions below.

Read both source drivers/macros and introductions. Low driver order: smoothing, low-tools, low-assembly, conclusion; all these operative TeX files now read in full (exact byte selections in private/reads.jsonl). High driver order: preparation, quantizers, walls, mesh, assembly, smoothing appendix; high body pending. Figures in low-tools and low-assembly read as complete TikZ definitions and captions; PDF visual inspection pending. A title metadata command in each driver was incidentally displayed in the macros selection; it supplies no mathematical evidence. No editorial acknowledgement material was detected in these low TeX files.

Domains are nonempty bounded connected open subsets of R3, maps are actual homeomorphic representatives in W1p, arbitrary topological orientation handled by target reflection. Smooth means on open domains, no boundary extension. Actual low assembly establishes local uniform convergence via cellwise small source displacement and small physical target supports. Fixed target follows from image-preserving cell reparametrization followed by fine-value proper-degree smoothing, not from a limit argument.

Low mechanism: retain compact Whitney jets of all positive ranks; source sampling and target tie budgets preserve derivative mass. Rank3 radial blocks install a tiny exact germ, expand its model to most of a cell, retain small shell costs via contracted spokes and (p2) weighted wedges. Rank1 uses constant-speed line near-minimal length with the explicit squared defect; rank2 p2 uses conformal disk parametrization with exact boundary and sharp area-to-energy; rank2 p<2 uses a second radial planar construction. Kernel collapse P_lambda tends to P0 with D_i DP0=D_i. Uncontrolled faces use disk (p2) or radial collapse (p<2); volumes use subcritical collapse p<3. Endpoint p1 uses no reflexive compactness.

Parameter order is substantive: compact bound M, shell l, sharp tolerances/J, thin target aspect eta, trace tau, jet delta and excess neighborhoods, source h and micro s, weights and target mesh, transfer H0, radial/attenuation/cap parameters, kernel lambda, summable cell completion. Subsequent uncontrolled Lipschitz constants may not multiply an earlier fixed tail. sm:bilip-pl fixes finite PL libraries before selecting small bad-cube volume; every library map is a compact PL embedding, so it has a finite inverse derivative bound too, although the stated estimate is forward only. PL smoothing has positive local determinant minima fixed before support shrinkage.

## Direction to test after high-source and primary readings

For a smooth orientation-preserving diffeomorphism g, inverse q-energy on its exact target equals integral_Omega |cof Dg|^q (det Dg)^(1-q) dx. For q=1 the determinant singularity cancels. Strong W1p convergence with p>=2 supplies strong L1 convergence of cofactors. To turn this into strong inverse W11 one still needs the precise area formula for the limiting representative, treatment of J=0, convergence in target measure of the inverse differential, and absence of singular inverse derivative mass. Neither mere formal matrix inversion nor small bad-set volume suffices. This may be a routine endpoint consequence once classical ingredients are supplied, not an additional nominee.

The radial completion q_{alpha,delta} sends most source radii into a thin target shell. Its inverse radial derivative is of order delta^-1 on target volume of order delta; its inverse q-energy therefore has a lower bound proportional to delta^(1-q) for q>1 in the identity-ball model. This is a concrete compatibility obstruction to copying the forward small-delta order, not a counterexample to existence of different simultaneous approximants. The full calculation and possible repairs remain to be written.

## Complete endpoint reduction after the primary comparison (prefreeze)

This is an auxiliary derivation, not a frozen nominee or a claim of literature novelty. The new target being tested is simultaneous strong forward and inverse W^{1,2} approximation on arbitrary bounded three-dimensional domains. The calculations below close its inverse-exponent-one boundary, and distinguish that boundary from the unresolved target. The historical Proposition P in i07, read before this derivation, assumes p>3 and positive Jacobian. Its statement and proof remain unchanged. The following calculation is not submitted for a new grade on that target. Grochulska's compact-image semicontinuity and area/Fatou argument, read in the course of the calculation, are the strongest direct primary comparison; the compact-image step below is that classical operation localized to Lipschitz pieces.

Let Omega,Lambda be nonempty bounded connected open subsets of R^3. Let f:Omega->Lambda be an orientation-preserving homeomorphism in W^{1,2}, with g=f^{-1} in W^{1,1}(Lambda). Let f_j:Omega->Lambda be orientation-preserving smooth diffeomorphisms, strongly convergent to f in W^{1,2} and locally uniformly. No boundary regularity, global uniform convergence, N or N^{-1} property, positive limiting Jacobian, or uniform distortion is assumed. Then the following argument gives g_j=f_j^{-1}->g strongly in W^{1,1}.

All matrix norms here are Frobenius. Put A_j=Df_j, A=Df, J_j=det A_j>0 and F_j=adj A_j=(cof A_j)^T. The polynomial inequality

    |adj B-adj A| <= C(|A|+|B|)|B-A|

and Cauchy-Schwarz give F_j->F=adj A in L^1(Omega). Thus the forward squared gradients and the cofactor densities are uniformly integrable. Also J=det A>=0 a.e., by convergence in measure and positivity of J_j. No assertion that J_j is uniformly integrable on all Omega is needed.

1. Inverse values. For x=g(y), choose a small ball U compactly contained in Omega, containing x and with y outside f(partial U). Uniform convergence on partial U and homotopy invariance of degree imply that, for j large and y' sufficiently near y, g_j(y') lies in U. Each g_j is a homeomorphism onto the *same* target, so there is exactly one such preimage. Shrink U and cover a compact target set by finitely many such neighborhoods. This proves g_j->g locally uniformly. Boundedness of Omega and finite measure of Lambda give global L^1 convergence of the values by dominated convergence. This is not a statement of global uniform convergence.

2. The inverse derivative is a pushforward measure. The ordinary smooth change-of-variables formula, with multiplicity exactly one, gives for every Borel E subset Lambda

    Dg_j(y) dy = (f_j)_#(F_j(x) dx),
    integral_E |Dg_j| = integral_{f_j^{-1}(E)} |F_j|.                 (E1)

In particular Dg_j is globally integrable, since F_j is. For every compactly supported continuous test matrix phi,

    integral phi(f_j(x)):F_j(x) dx -> integral phi(f(x)):F(x) dx.

The first error uses F_j->F in L^1; the second uses bounded phi, pointwise convergence of f_j, and dominated convergence with |F|. Distributional convergence from g_j->g in L^1 identifies the limiting finite matrix measure:

    Dg(y) dy = f_#(F(x) dx).                                      (E2)

The hypothesis g in W^{1,1} is used here. It excludes a singular inverse derivative measure; it is not deduced from mere topological invertibility. An injective Borel pushforward preserves total variation: writing F=sigma |F|, its polar vector after pushforward is sigma composed with g and still has norm one. Therefore

    |Dg(y)| dy = f_#(|F(x)| dx),
    integral_E |Dg| = integral_{f^{-1}(E)} |F|.                    (E3)

This is an identity of Borel measures on the open target. Images of Borel sets under the homeomorphism are Borel. Completion handles arbitrary measurable sets after the identities are established. There is no unproved global change-of-variables substitution for f in (E2).

3. Zero-Jacobian sets have no cofactor mass. A Sobolev map has a countable Lipschitz decomposition covering the source up to a null set, with the weak derivative equal to its approximate derivative a.e. On each Lipschitz piece E_i, the injective area formula applies with multiplicity one. In particular f(E_i intersect {J=0}) has volume zero. Applying (E3) and absolute continuity of |Dg|dy gives

    integral_{E_i intersect {J=0}} |F| = 0.

The omitted source null set has no |F|dx mass. Hence F=0 a.e. on {J=0}. This proves the needed finite *inner* distortion condition, rather than presuming that Df=0 there. In three dimensions rank-one gradients are allowed by this conclusion. It also identifies precisely why division by J is harmless only after removing zero-cofactor mass. It is not a claim that f has global N.

4. Compact regular pieces pay the determinant. Given eta>0, choose a compact K contained in finitely many Lipschitz pieces of {J>0}, with

    mu(Omega\K) < eta,  mu=|F|dx.

One can first make the pieces disjoint, restrict them to compact subsets, and take a finite union. Their images are compact, and the injective area formula holds on K. Neither a collar nor an extension operator for Omega is involved. Uniform convergence on K implies, for every delta>0 and j large,

    f_j(K) subset (f(K))_delta,
    limsup |f_j(K)| <= |f(K)| = integral_K J.

Convergence A_j->A in measure, extraction of a.e. subsequences, Fatou, and smooth area on K give the opposite liminf for integral_K J_j=|f_j(K)|. Thus

    integral_K J_j -> integral_K J,
    J_j -> J in L^1(K),
    |f_j(K) symmetric-difference f(K)| -> 0.                      (E4)

For the second assertion use the nonnegative Scheffe argument: min(J_j,J)->J in L^1 by domination and convergence in measure, and expand |J_j-J|. For the third, the excess f_j(K)\f(K) lies in arbitrarily thin outer neighborhoods of a compact set; equality of limiting volumes then controls the missing part. This does not prove global L^1 convergence of the determinants when N fails. It is the compact-image/Fatou mechanism in Grochulska, Lemma 16 and the proof of Theorem 6, applied only on sets where area equality is legitimate.

5. Strong inverse derivatives on the moving images. Set G=Dg. On K, (E2) and area equality imply

    F(x)=G(f(x))J(x) a.e. on K.                                  (E5)

Equivalently, wherever J>0 these are the ordinary approximate inverse matrices; one may also obtain this by restricting both maps to their Lipschitz differentiability pieces. No matrix inverse is assigned at J=0. Choose a compactly supported continuous matrix field G_c on Lambda with ||G-G_c||_1<epsilon. Such fields are dense in L^1 on every open set, independently of boundary geometry. By (E1),

    integral_{f_j(K)} |Dg_j-G|
      = integral_K |F_j-G(f_j)J_j|
      <= integral_K |F_j-G_c(f_j)J_j| + ||G-G_c||_1.

The first integrand converges in L^1 to |F-G_c(f)J|, using F_j->F, (E4), boundedness of G_c and uniform convergence on K. By (E5) its integral is at most ||G-G_c||_1. Let epsilon->0. Consequently

    integral_{f_j(K)} |Dg_j-G| -> 0.                              (E6)

6. Both bad-set budgets. Outside f_j(K),

    integral |Dg_j-G|
      <= integral_{Omega\K}|F_j| + integral_{Lambda\f_j(K)}|G|.

The first term tends to mu(Omega\K). By (E4) and absolute continuity of the integral of G, the second tends to integral_{Lambda\f(K)}|G|=mu(Omega\K). Thus limsup ||Dg_j-G||_1<=2eta, and eta is arbitrary. This proves the claimed endpoint convergence. It also explicitly yields inverse uniform integrability: for target E, use (E6) on E intersect f_j(K), then bound the complementary inverse mass by mu_j(Omega\K). Choose K, then a sufficiently late j, then |E| small, and finally handle the finite initial family individually. Forward uniform integrability comes from strong L^2 convergence. No reflexivity at the inverse exponent one is used.

For every finite p>=2, strong W^{1,p} implies strong W^{1,2} on bounded Omega. The source constructions allow a locally uniformly convergent sequence with the required forward strong norm. Therefore the calculation yields simultaneous (p,1) approximation whenever f^{-1} is W^{1,1}. By interchanging source and target it also gives the pair (1,q) when q>=2; it does not by interpolation supply all intermediate (p,q). Orientation reversal is handled by one fixed target reflection, preserving all norms, and then reflecting back. The calculation is an executed source/classical combination, not an additional claimed substantial result.

## What survives at inverse exponent q>1

For a smooth positive diffeomorphism u, exact change of variables gives

    integral_Lambda |D(u^{-1})(y)|^q dy
      = integral_Omega |adj Du(x)|^q (det Du(x))^{1-q} dx.          (Q1)

The exponent is 1-q, not -q. The Jacobian factor from target volume is essential. For h=v composed with S, a target self-diffeomorphism written h=S composed with v,

    D(h^{-1})(S(y)) = D(v^{-1})(y) DS(y)^{-1},
    E_q(h^{-1}) = integral_Lambda |D(v^{-1})(y)DS(y)^{-1}|^q det DS(y) dy.

For h=v composed with R with a source self-diffeomorphism R,

    D(h^{-1})(y)=D(R^{-1})(v^{-1}(y))D(v^{-1})(y).

Neither formula is estimated merely by the small support measure. All maps in these formulas are locally bi-Lipschitz or smooth, so the chain and area formulas genuinely apply. For a limiting Sobolev homeomorphism the formulas must first be restricted to regular Lipschitz pieces; any singular image set and zero-Jacobian set require separate treatment as in (E2)-(E5).

The endpoint proof fails at a precise place for q>1. Strong cofactors control mu_j=|F_j|dx, whereas the required density is nu_j=|F_j|^q J_j^{1-q}. Even on a regular compact K where J_j->J in L^1, this does not control a negative power of small J_j. The missing estimate is uniform integrability (and correct limiting mass) of nu_j, not merely convergence of J_j in measure or positivity of each J_j.

The radial profile used by the source's low-exponent collapse and by high-preparation's hide-cubes makes this visible quantitatively. In a unit ball, let

    R(r)=(1-delta)r/alpha                 (0<=r<=alpha),
    R(r)=1-delta+delta(r-alpha)/(1-alpha) (alpha<r<=1).

Its singular values on the outer shell are a=delta/(1-alpha), b=R/r twice. On any fixed subannulus r in [1/2,3/4] with alpha<1/4 and delta<1/4, b is bounded above and below by positive constants. The inverse q-energy there is bounded below by

    c_q integral a^{1-q} b^2 r^2 dr >= c'_q delta^{1-q}.

Thus taking delta to zero after fixing alpha, as the forward proof permits, diverges for every q>1. Smoothing the radial corner on a disjoint thin annulus changes neither this lower bound nor injectivity. In a physical source cell of radius r_0 and comparable target radius R_0 the dimensional factor is r_0^q R_0^{3-q}; the bad factor remains delta^{1-q}. The forward inner cost has the source's factor alpha^{3-p}. Its vanishing does not cancel the displayed outer inverse cost.

For an affine normal compression diag(1,...,1,lambda,...,lambda) with k unchanged tangential dimensions and 3-k compressed ones, the inverse q-density scales as lambda^{3-k-q} on the fixed source box (up to constants depending on q). In particular a flattened sheet k=2 has lambda^{1-q}. This is exactly the geometry of strict openings of two-dimensional quantizer faces. It is not valid to infer inverse control from the forward upper Lipschitz bound. The high proof's snapping map also explicitly controls J_D=R_D^{-1}K_D in the forward direction only; its inverse is allowed an arbitrary finite bound after the configuration is fixed.

The historical i07 Proposition Q already proves failure of automatic q>1 control for smooth forward sequences converging to the identity in every finite W^{1,p}. We do not offer a renamed version. The calculations above diagnose the *actual source operations*, not nonexistence of a different sequence.

## Fully executed compatible subclass: locally bi-Lipschitz inputs

Suppose H is locally bi-Lipschitz, H in W^{1,p}(Omega), H^{-1} in W^{1,q}(Lambda), 1<=p,q<infinity. The source's finite-library PL approximation can carry both budgets. Here is the extra bookkeeping, rather than an assumption of uniformly bounded inverse libraries for arbitrary Sobolev inputs.

Fix the source's locally finite coarse neighborhoods U_P, local bi-Lipschitz constants K_P, finite normalized configurations, and finite number of colored insertion stages. On every stored PL embedding, each full-dimensional affine gradient is invertible. Finitely many pieces on each compact normalized patch give both a forward bound M_P and an inverse-matrix bound N_P. Finitely many stored models and finitely many interacting coarse indices preserve these finite bounds. They are fixed *before* reducing the fine resolution, just as M_P is in the source. They need not be uniform in P or efficiently bounded by K_P.

Use local good-cube derivative tests with exponent r=max(p,q), which are available because DH is locally bounded. Choose their tolerances summably after all local conversion constants. On good cubes the interpolant L has gradients within C delta_P of an affine A_Q whose smallest singular value is >=(2K_P)^{-1}. Reducing delta_P first gives a uniform local inverse bound and

    |(DL)^{-1}-(DH)^{-1}| <= C K_P^2 |DL-DH|

a.e. there. Local boundedness converts the good-cube r-error into the required p and q errors with the already fixed weights. To compare inverse derivatives at their *actual target points*, set G=DH^{-1}. Under the common local forward and inverse bounds, the image and preimage measures of exceptional Lusin sets are bounded by fixed constants times their measures. Approximate G in L^q on the relevant compact target neighborhood by a continuous bounded field, use uniform value closeness of L to H for its compositions, and then the preceding inverse-matrix estimate. Thus the good-cube inverse error tends to zero, with no implicit identification of G(L(x)) and G(H(x)).

On bad cubes B_P, the final PL map V is one of the stored models, so

    integral_{V(B_P)} |DV^{-1}|^q <= N_P^q M_P^3 |B_P|,
    integral_{B_P}|DV|^p <= M_P^p |B_P|.

Moreover V(B_P) lies in a fixed relatively compact target neighborhood on which H^{-1} has bounded derivative, hence

    integral_{V(B_P)} |DH^{-1}|^q <= K'_P{}^q M_P^3 |B_P|.

Choosing |B_P| below summable budgets divided by these fixed constants pays both maps. All final derivatives come from stored models; intermediate ambient insertion derivatives are not used. Image sets of disjoint source cubes are disjoint, so the target estimates sum without multiplicity. Local choices are assembled over the same finite-stage locally finite source construction, which preserves exact target at every insertion. Fine value tolerances imply inverse values locally uniformly and, after choosing separate summable target budgets, in L^q; bounded domains also permit dominated convergence along a sequence. Thus V can be chosen simultaneously close in the two Sobolev norms and with finite global energies for both maps.

Campbell-D'Onofrio-Vitek, Theorem A and its complete three-dimensional proof, then smooth V with both errors arbitrarily small and the same target. Their local face/edge/vertex models have finite bounds M and K for derivatives and inverse derivatives fixed before common support shrinking. The forward changed volume tends to zero, its image volume is <=M^3 times that volume, and the inverse cost is charged with K^q. Their locally finite annular assembly uses summable budgets and slowly varying radii. This is a fully compatible application. It neither imposes a global bi-Lipschitz bound nor provides such a bound for the approximants. It supplies no passage from arbitrary bi-Sobolev input to a locally bi-Lipschitz approximation with both energies.

## Compatibility and a nonvacuous exact family

For the prospective (2,2) target, apply Csornyei-Hencl-Maly Theorem 4.5 twice: f in W^{1,2}, g in W^{1,1} implies g has finite distortion; g in W^{1,2}, f in W^{1,1} implies f has finite distortion. Thus Df=0 a.e. on {J_f=0}, and Dg=0 a.e. on {J_g=0}. Rank-one or rank-two positive-energy pieces cannot be advertised as extra freedom in this joint class. This removes the source's positive deficient-rank saturation contribution, but does *not* make its uncontrolled residual opening inverse-cheap. It is still necessary to fill the complementary regions while controlling both measures.

The class is nonempty beyond locally bi-Lipschitz maps. On B=B(0,1) in R^3 take f_alpha(x)=|x|^{alpha-1}x, alpha>0, with f_alpha(0)=0. It is an orientation-preserving homeomorphism B onto B, inverse f_{1/alpha}. Away from zero its singular values are alpha r^{alpha-1}, r^{alpha-1}, r^{alpha-1}. Its exact integrability conditions are

    3+p(alpha-1)>0,
    3 alpha+q(1-alpha)>0.                                       (R1)

For p=q=2, every alpha>0 is allowed. If alpha differs from one, one direction fails local bi-Lipschitzness at zero. In particular there is no vacuous incompatible parameter regime in this example.

The simultaneous construction for this family is explicit. Choose a smooth positive a(t) equal to 1 for t<=1 and to alpha for t>=2, and put

    phi(t)=2^alpha exp(-integral_t^2 a(s)/s ds), 0<t<=2;
    phi(t)=t^alpha, t>=2; phi(0)=0.

Then phi(t)=c_alpha t near zero, phi'>0, and it is smooth with the specified exact match near 2. Replace r^alpha by R_epsilon(r)=epsilon^alpha phi(r/epsilon) for r<2epsilon, keeping r^alpha outside. The radial map f_{alpha,epsilon} is a smooth orientation-preserving diffeomorphism of B onto B, linear and nonsingular at zero, and unchanged outside B(0,2epsilon). Its inverse modification is supported in B(0,(2epsilon)^alpha). The two errors obey

    ||D f_{alpha,epsilon}-D f_alpha||_p^p
      <= C_{alpha,p} epsilon^{3+p(alpha-1)},
    ||D f_{alpha,epsilon}^{-1}-D f_alpha^{-1}||_q^q
      <= C_{alpha,q} epsilon^{3 alpha+q(1-alpha)}.

Indeed on the source core all approximating singular values are bounded above by C_alpha epsilon^{alpha-1} and below by c_alpha epsilon^{alpha-1}; use the exact limiting radial integrals for the other terms. Change variables, or integrate in the target radial coordinate, for the second estimate. The value errors are <=C_alpha epsilon^alpha and <=C_alpha epsilon respectively. Both exponents in (R1) being positive proves both strong convergences. This elementary subclass is not offered as a substantive extension; it demonstrates compatible examples and the dimensional source/target budget which a general local replacement would need.

## The integrated (2,2) attempt and the remaining operation

The strongest compatible chain actually executed is:

1. Joint W^{1,2} hypotheses force finite distortion on each side by CHM. Capture the derivative energies of both maps on finitely many compact regular pieces; use (E2)-(E5) and the inverse area formula on regular pieces, not a global N assertion.
2. On such pieces choose finite affine jets with positive minimum singular values. Their source and target compact images have positive separations after taking disjoint compact subsets. Affine corrections and the source's local scale freedom can fit prescribed finite budgets there. The source's full-rank correction already permits fine exact inner cubes and arbitrary shell budgets *for the forward norm*.
3. If a locally bi-Lipschitz intermediate with both small errors existed, the preceding finite-library argument and CDV smoothing would finish globally with exact target and summable two-sided errors. Thus smooth finalization is paid in full.
4. On the complement, the source obtains its forward bound by carrier collapses, qualitative openings, strict target parameters, wall realization and (for 2<p<3) radial hiding. The (2,2) input's absent positive deficient ranks does not bound inverse gradients of these replacements. Trying to choose strict parameters last leaves the negative-power term in (Q1); choosing them first fixes geometry before the forward exceptional-set budget has been obtained. The present derivation has no estimate that resolves this dependency.

The exact unresolved obligation is a relative local filling/approximation operation on the actual paired source/target complementary regions, agreeing with the already installed affine cores and with compatible interfaces, which supplies BOTH

    integral_{bad source} |Du|^2 <= prescribed budget,
    integral_{bad target} |Du^{-1}|^2 <= prescribed budget,

with constants fixed before the remaining small regions and strict parameters are selected. It must preserve injectivity, the exact images, local finiteness, and the two summable budgets under exhaustion. No such operation is proved here. Merely applying the source to f and to g independently produces two unrelated maps; it does not make either inverse equal to the other. Alternating the two replacements has no proved control on the energy disturbed at the next step. The explicit collapse calculation shows why small volume or forward norm alone cannot supply the missing estimate. It does not prove the desired operation impossible.

No exact full-scope statement/proof was frozen for submission. This is PREFREEZE/no nominee, retaining the complete auxiliary reductions and this precise unresolved obligation. No correctness, contribution, acceptance or count is assigned.

## Ordinary energies versus constrained energies

For completeness, if W(x,A) is a Caratheodory integrand with |W(x,A)|<=a(x)+C|A|^p, a in L^1, strong W^{1,p} convergence implies W(x,Df_j)->W(x,Df) in L^1. The pointwise convergence follows along every a.e. convergent subsequence by continuity; the bound and uniform integrability of |Df_j|^p give uniform integrability, so Vitali and the subsequence principle give the full conclusion. This elementary source consequence is paid. The same argument allows a value variable with controlled p-growth.

Cofactors converge strongly in L^{p/2} for p>=2 and determinants in L^{p/3} for p>=3 by their polynomial difference inequalities and Holder. At lower p these strong-integrability conclusions are not available merely by writing the polynomials. The distributional determinant need not equal the pointwise determinant density and is not substituted for it here. Energies with inverse powers of det or the density (Q1) are outside ordinary p-growth. Positive approximating determinants do not give a uniform positive lower bound. Exact incompressibility, prescribed determinant, global boundary equality and parametric continuity have not been constructed. No smooth correction theorem is transferred to an arbitrary rough domain by name.

## A compatible two-sided repair which does work, and its exact limit

The failure of one-sided radial hiding does not rule out simultaneous conjugation. Let H:B(0,1)->B(0,1) be a smooth diffeomorphism equal to the identity on an open boundary collar. For 0<t<1 set

    H_t(x)=t H(x/t) if |x|<t, and H_t(x)=x otherwise.

Because H equals the identity on a collar, the definitions agree smoothly across |x|=t. The inverse is exactly the same construction with H^{-1}. Both maps preserve the ball and orientation. For every finite p,q,

    integral_B |DH_t-I|^p = t^3 integral_B |DH-I|^p,
    integral_B |DH_t^{-1}-I|^q = t^3 integral_B |DH^{-1}-I|^q,
    integral_B |H_t-x|^p = t^{p+3} integral_B |H-x|^p,
    integral_B |H_t^{-1}-x|^q = t^{q+3} integral_B |H^{-1}-x|^q.

These are exact substitutions; neither reciprocal determinant nor a large derivative of a radial transition appears. On B(x_i,r_i), multiply the derivative integrals by r_i^3 and the value integrals by r_i^{p+3} or r_i^{q+3}. On a locally finite disjoint family, choose t_i only after both finite model energies are known, making the sums smaller than prescribed budgets. The target supports are the same shrunken balls, so injectivity and exact image survive all gluings. Affine conjugation has only the fixed forward and inverse matrix factors of that affine map.

This is a positive classical alternative to the failed one-sided collapse. It shrinks a collar-fixed *self-map* toward the identity. It does not approximate a specified nontrivial boundary correspondence, and it does not produce that correspondence with controlled forward and inverse energy. An arbitrary residual source region and its target image need not be paired round balls or have an affine matching collar. Turning their already prescribed boundary map into the collar-fixed setting is precisely the unproved two-sided filling operation. Postulating such a quantitative conjugacy would assume the missing result. Thus this repair is used at its actual scope and is not dismissed merely because the first radial attempt failed.

For completeness, the joint regular-energy capture in the (2,2) attempt is legitimate despite possible failure of N. By CHM both maps have finite distortion. Almost every target point with Dg nonzero has J_g>0. The area inequality for g implies that the preimage under g of the source exceptional null set has zero measure on {J_g>0}. At the remaining matched approximate differentiability points, the inverse derivative identity holds on Lipschitz pieces. Consequently all nonzero forward and inverse energy is concentrated on matched regular pieces. Taking disjoint compact subsets and truncating the two finite energy measures captures both budgets. This fact removes a possible incompatibility in the good sets; it does not control the energy of a newly chosen filling on their complement.
