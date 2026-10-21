# PREFREEZE derivation: quadratic reweighting of subgaussian log-concave laws

Codex / GPT-6 Astra / high / default service tier. Source093 is the single selected family. This is a feasibility notebook and strongest-reduction comparison, not a frozen prospective theorem, nomination, correctness/contribution grade, or new-to-literature claim. The original r83 Gaussian Lipschitz-transport question and r118 full conditioning comparison remain unchanged. The pin and its operative proofs are stipulated true.

## 1. Actual interfaces and the question tested

Source093, `build/sections/01-introduction.tex`, `thm:main`, assumes a centered log-concave Lebesgue law mu on R^d with

    sup_{|theta|=1} E exp(<theta,X>²/a²) <= 2

and supplies Ent_mu(f²) <= C093 a² E_mu|grad f|², with an absolute constant. Put R0=C093 a²/2, using Ent<=2R0 energy. The source calculus proves the curvature criterion with convex extended-valued potentials, tensorization/convolution, Herbst, and entropy dissipation. Its transport-entropy corollary is already explicit. None of these interfaces asserts uniform control under every linear or quadratic reweighting.

The source's observations `prop:information-upper` is more specialized still: a limsup statement for covariance observations of the near-extremal matrix fields in its contradiction sequence. Time and cap are fixed before that limit. Its likelihood calculation is averaged over observation outputs. It cannot be evaluated at an arbitrary rare conditioning label to obtain a uniform posterior estimate. The full source critical/prediction/hierarchy/matrix proof was not reread; this is not a truth audit or a claim of complete source-proof coverage.

The initial transport thought was stopped after reading the actual r83 derivation. Its all-dimensional map question was not weakened or renamed. The different feasibility question considered here was whether a small positive quadratic weight

    dnu_B = Z_B^(-1) exp(<x,Bx>/2) dmu,  B >= 0,

could retain a dimension- and rank-independent LSI merely from the source hypotheses and small a²||B||. The weight is centered at the original barycenter; arbitrary linear terms are not smuggled into B. This was an exploratory possibility, not a frozen claim. Sections 2–3 pay the strongest compatible standard reductions. Sections 4–8 exhibit an explicit obstruction to that particular uniform conclusion.

## 2. Stronger primary comparison, including the sign

Barthe–Milman, arXiv:1202.5318v1, Theorem `thm:log-Sob-trans` (Theorem 2.4), is stronger than the bounded-density Holley–Stroock argument. In their inverse-constant convention rho=1/R0, it transfers LSI to a target with curvature >=-kappa, assuming rho>4p kappa/(p-1) and an Lp bound L on the normalized density ratio. Their proof transfers concentration by density-ratio truncation, then uses concentration-to-isoperimetry under the target curvature bound, and Gaussian isoperimetry-to-LSI. Its dependence on L is real; dropping L is not a permissible specialization. The p=2 case requires beta R0<1/8 when kappa=beta.

Their operative proof and the relevant original Milman curvature proof were read at the ranges in READING-LIMITS.md. The geometric transitive inputs and final Ledoux/Beckner implication were not all reread in their original publications. They are credited classical inputs, not newly proved claims.

Bizeul, arXiv:2306.12997v3, `prop_760`, already addresses NEGATIVE-quadratic Gaussian damping exp(-t|x|²). It gives an upper bound through the L2 density ratio and norm concentration, combined with positive curvature, and states sharp covariance deterioration. Its example is the uniform law on

    sqrt(3) B_infinity^n x R intersect
    { (x,l): |x| <= sqrt(n)+C0(1-|l|) }.

The paper states the geometric estimates and explicitly omits their detailed sharpness calculation. I have not silently filled those omitted calculations or represented them as a full proof I read. Its upper-bound proof, centered Gaussian-tilt reduction, and strong-tilt interfaces were read. Its negative-quadratic sign and the cap 1/t matter. This comparison prevents treating general Gaussian-conditioning instability as a new finding.

The present positive-quadratic calculation uses exact Gaussian integration to supply its own scalar marginal; it does not infer the opposite sign by changing a symbol in Bizeul's conclusion. The Gaussian determinant, convex perspective, and scalar exponential tilt are classical operations. Combining them below is useful feasibility work, but a distinct formula is not by itself substantial-contribution evidence.

## 3. What is paid for finite rank, including normalization and approximation

Fix B>=0 of rank r, beta=||B||. Source Herbst gives

    E_mu exp(<h,X>) <= exp(R0 |h|²/2).

For standard Gaussian G on the range of B, Tonelli and the elementary Gaussian moment-generating identity give

    E_mu exp(p<X,BX>/2)
      = E_G E_mu exp(sqrt(p)<B^(1/2)G,X>)
      <= det(I-p R0 B)^(-1/2),

provided pR0 beta<1. This is a complete compatible Gaussian augmentation, not an unjustified interchange of signed integrals. It proves finiteness of the partition function. Since Z_B>=1,

    ||dnu_B/dmu||_L2(mu)
       <= det(I-2R0 B)^(-1/4)
       <= (1-2R0 beta)^(-r/4).

If mu=e^-V with V convex smooth, the target potential V-<x,Bx>/2 has Hessian >=-beta I. Barthe–Milman therefore gives a finite LSI bound depending only on R0,beta,r whenever beta R0<1/8. This is already a complete dimension-free-in-the-ambient-dimension reduction for fixed rank. No uniform LSI of every conditional linear tilt is needed. Failure of an all-tilt covariance shortcut does not invalidate this direct transference.

For the nonsmooth source class, use mu_s=mu*N(0,sI). Source calculus gives smooth log-concavity and LSI constant at most R0+s, and preserves centering. For example beta R0<=1/32 and 0<s<=R0 give uniform slack in both the p=2 curvature condition and Gaussian determinant estimate. Couple X_s=X+sqrt(s)G. Then X_s->X almost surely. The same determinant estimate at a higher fixed moment (p=4 suffices here) gives uniform integrability of exp(<X_s,BX_s>/2), so partition functions and compact-test integrals converge. The smooth target LSIs have a common bound depending only on R0,beta,r. For compact smooth f, entropy and energy converge, giving the target inequality in the limit. Thus nonsmooth support is not an unpaid compatibility step in this small-beta regime.

This baseline carries rank dependence through the normalized density ratio. The fact that the displayed upper estimate grows with rank does NOT prove rank-independent bounds impossible. The following construction is what tests that claim.

## 4. Exact covariance modulation: all parameters and the joint law

Use the actual old r83 scalar ingredient, with explicit credit. For R>=2 define the even C1 convex potential V_R(y)=v_R(|y|), where

    v_R(u) = u²                                      (0<=u<=R),
             2Ru-R²                                 (R<=u<=2R),
             3R²+2R(u-2R)+(u-2R)²                    (u>=2R).

The inequalities (2/3)y²<=V_R(y)<=y² follow directly from these pieces. On [R,2R], 2Ry-V_R(y)=R². This plateau and its scalar tilt are not new results of r142.

For any 0<beta<=1/4 choose an integer

    n >= 10^6 R^4/beta²,
    k = 4R(1-beta)/(n beta),
    delta = 2n k²,
    s(y)=1+k y,             -3R<=y<=3R.

Define a probability mu on R x R^n by first taking Y with density

    Z_Y^(-1) 1_{[-3R,3R]}(y) exp(-V_R(y)-delta y²/2),

and then, conditionally on Y=y, taking Z~N(0,s(y) I_n). Its Lebesgue density is therefore proportional to exp(-U(y,z)) on the slab, where

    U(y,z)=V_R(y)+delta y²/2+(n/2)log s(y)+|z|²/(2s(y)).

The factor (n/2)log s is essential. Omitting it would change the Y marginal by s(y)^(n/2) and lose centering and the uniform original marginal scale. All normalizing factors are finite and positive.

Our choices imply |ky|<=12R²/(n beta)<1/2, hence 1/2<=s<=3/2, and delta<=32/(10^6 R²)<1/100. The actual bounds have much more slack.

## 5. Log-concavity and original subgaussian scale

The quadratic-over-linear function |z|²/(2s(y)) is convex on the slab. For a tangent increment (u,w), its Hessian quadratic form is exactly

    (1/s) |w-(k/s) z u|² >= 0.

The remaining scalar function A(y)=V_R(y)+delta y²/2+(n/2)log s(y) has, away from the two piece boundaries,

    A''(y)=V_R''(y)+delta-(n/2)k²/s(y)² >= 0,

because V_R''>=0, s>=1/2, and delta=2nk². The derivative of V_R is continuous at its joins, so the same convexity holds distributionally across them. Adding the convex slab indicator completes the log-concavity proof. The support has nonempty interior and the law has a Lebesgue density.

Y is symmetric, and E[Z|Y]=0. Thus (Y,Z) is centered even though its joint law need not be centrally symmetric. Also E s(Y)=1, so Cov(Z)=I_n and Cov(Y,Z)=0.

Here is a uniform marginal bound without appealing to the theorem being tested. Since R>=2,

    Z_Y >= exp(-delta/2) integral_{-1}^1 exp(-y²)dy
        >= (4/3) exp(-1/200),

using exp(-y²)>=1-y² on [-1,1]. Since V_R>=2y²/3,

    E exp(Y²/16)
      <= sqrt(pi/(2/3-1/16)) / [(4/3) exp(-1/200)] < 2.

For any (p,v) with p²+|v|²=1, Cauchy–Schwarz and (a+b)²<=2a²+2b² give

    E exp((pY+<v,Z>)²/64)
      <= [E exp(p²Y²/16)]^(1/2)
         [E exp(<v,Z>²/16)]^(1/2).

Conditioning on Y, the second expectation is at most

    (1-3/16)^(-1/2) < 2,

because s<=3/2 and |v|<=1. The first is at most 2. Their square-root product is therefore at most 2. The source parameter a=8 works for every R,beta,n in this construction. Source093 supplies the same base entropy coefficient 64 C093 for all of them. That use of the source is exact and within its stated hypotheses.

## 6. A small quadratic weight becomes a large scalar tilt

Now multiply mu by exp(beta|z|²/2) and normalize; equivalently B=diag(0,beta I_n), of operator norm beta. Since beta s<=3/8, Gaussian integration is legitimate and gives exactly

    E[exp(beta|Z|²/2)|Y=y]=(1-beta s(y))^(-n/2).

Consequently the Y marginal of nu_B is proportional to

    1_{[-3R,3R]} exp(-V_R(y)-delta y²/2)
                         (1-beta s(y))^(-n/2).

Because 1-beta s(y)=(1-beta)(1-4Ry/n), the y-independent factor disappears on normalization. Set

    D(y)=-(n/2)log(1-4Ry/n)-2Ry-delta y²/2.

For |u|<=1/2, 0<=-log(1-u)-u<=u². Here u=4Ry/n and |u|<=12R²/n<1/2, so on the ENTIRE slab

    |D(y)| <= 8R²y²/n + delta y²/2
            <= 72R^4/n + 144R^4/(n beta²)
            <= (72 beta²+144)/10^6 < 1/100.

This is a global normalized-density comparison, not a local Taylor approximation near the plateau. If tau_R denotes the probability proportional to

    1_{[-3R,3R]} exp(2Ry-V_R(y)),

then the Y marginal of nu_B has Radon–Nikodym derivative relative to tau_R between exp(-2/100) and exp(2/100). The same bound holds after the two different normalizations because both are integrals of factors between exp(-1/100) and exp(1/100).

Thus the small quadratic perturbation has implemented, to fixed multiplicative accuracy, the large linear tilt 2R of the old scalar example. It did so while preserving centering, log-concavity and uniform linear subgaussian scale of the ORIGINAL joint law. Directly adding a linear term to a purported small centered quadratic would not establish this.

## 7. Actual spectral deterioration, not merely a failed proof bound

On [R,2R] the unnormalized tau_R density is exp(R²). Its full untruncated normalizer is at most

    exp(R²)(R+sqrt(pi)) + 1/(2R) <= 2R exp(R²),  R>=2.

Indeed [0,R] and [2R,infinity) contribute half-Gaussian tails around R and 2R respectively, and on the negative half-line 2Ry-V_R(y)<=2Ry. Truncation to [-3R,3R] can only reduce that normalizer.

The intervals A=[R,5R/4] and B=[7R/4,2R] each have length R/4, so tau_R(A),tau_R(B)>=1/8. The preceding normalized-density comparison gives nu_B(Y in A),nu_B(Y in B)>=1/16. Their distance is R/2. With independent copies Y,Y',

    Var_nu_B(Y)=(1/2)E(Y-Y')²
       >= nu_B(A) nu_B(B) (R/2)²
       >= R²/1024.

The optimal Poincaré constant of the JOINT tilted law is at least this variance because the coordinate Y has gradient norm one. For compact smooth test conventions, first approximate the bounded Y-coordinate on the fixed slab and use cutoffs in z; the tilted conditional Gaussians have uniformly bounded covariance for each fixed construction, so the cutoff energies vanish. An entropy coefficient K in Ent(f²)<=K energy must obey K>=2 Var_nu_B(Y) by linearization and the same finite-energy approximation. Thus a uniform bound independent of n and R cannot hold for this positive-quadratic class, even at any fixed beta in (0,1/4].

If an isotropic base is desired, let v=Var_mu(Y). The same integral bounds give 1/64<=v<=2: for the lower bound use |y| in [1/2,1], Z_Y<=3 and exp(-V_R-delta y²/2)>=1/4 there; for the upper bound integrate y² exp(-2y²/3) and use Z_Y>1. The linear map (y,z)->(y/sqrt(v),z) makes mu isotropic and keeps a universal linear subgaussian parameter (a=64 suffices). B is unchanged because it acts only on z. The new tilted coordinate variance is at least R²/2048. This is ordinary affine normalization of the same diagnostic, not another proposed result.

No assertion is made that the tilted law remains log-concave, has infinite Poincaré constant for a fixed R, or violates the fixed-rank transference bound. The rank n grows; the small operator norm does not make the quadratic weight globally bounded or Lipschitz. The scalar marginal after tilting is close to a long nearly uniform interval, so the obstruction is an actual spread of probability, not a fictitious singularity of a conditional decomposition.

## 8. Reconciliation with the strongest compatible operations

Gaussian augmentation is exact, but it weights linear-tilt laws by their own partition functions. Their covariance/LSI cannot be replaced by those of the original mu. The r83 all-tilt warning remains relevant, while the new computation checks the actual centered quadratic and joint geometry rather than stopping at that warning.

Barthe–Milman applies whenever beta is small enough compared with the common original LSI constant, but its density-ratio factor grows with n. The diagnostic does not contradict that theorem; it explains why its rank-free deletion is invalid. Source093's averaged covariance-observation estimates do not control this rare-event reweighting without the missing normalization cost. Bizeul already shows that a naive claim of universal stability under Gaussian damping is untenable, with a different sign and curvature cap. None of these compatible inputs is ignored in order to manufacture an unpaid lemma.

This resolves the tested rank-independent positive-quadratic extrapolation NEGATIVELY at the level of supporting feasibility mathematics. It does not solve the old full Gaussian Lipschitz-transport question, improve the full source theorem, or nominate an obstruction as a replacement for an old failed target. Finite-rank bounds, convex conditioning, bounded perturbations, and strong-tilt consequences are already paid by the cited operations.

## 9. Stopping disposition

PREFREEZE / no nominee. There is no feasible substantial theorem frozen in this round. The source theorem, r83 scalar plateau, classical perspective construction, exact Gaussian determinant, and primary transference comprise the actual reduction. I have not established an additional substantial operation beyond that composition or a literature contribution for the diagnostic. No new grade is requested for r83, r118, I05 or I147, and no old full scope is narrowed.

The proposed rank-independent stability conclusion is not left as an open gap: the displayed family obstructs it. What is NOT supplied is a full new substantial result with completed operative-source/transitive/literature comparison. A different positive stability theorem would need additional structural assumptions compatible with this example and a nonroutine argument; no such weakened substitute is formulated or nominated here. No impossibility of other analytic directions, worldwide-open assertion, priority claim, or family exhaustion follows.
