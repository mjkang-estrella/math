# I301 — independent adversarial review of U300

2026-10-13. **Proof verdict: PASS unchanged for U300.** This is a mathematical review, not an acceptance, contribution, priority, or count claim. The audited parent analysis has SHA256 `a00cd592d623d7b9b1cc5be06a3fd3c96f09de8cc0fc933295e68238fa75af1e`. No repair or restriction of its theorem is required. Details below expand its regularity justifications without changing its mechanism or premises.

## 1. Exact target and proof dependencies

Let gamma be standard Gaussian probability on R, and

    Q_r w(x)=E w(r x+sqrt(1-r^2) Z),  0<r<1,
    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    V(t)=atanh(t),  L=log 2,
    I(w)=E_gamma psi(w)-psi(E_gamma w),
    f_r(J)=psi(r psi^{-1}(J)),  0<=J<=L.

Nonconstant means nonconstant modulo Gaussian-null sets. Endpoint entropy is interpreted by continuity, including 0 log 0=0. The verified assertion is

    I(Q_r w)<f_r(I(w))

for every measurable w:R->[-1,1] with 0<I(w)<L and every 0<r<1. Bias, input endpoint values, arbitrary measurable tails, nonmonotone kernels, and all open amplitudes are included. Neither an effective deficit constant nor strictness at J=0 is asserted.

Only the pinned cube theorem `main:soft` is stipulated in the core proof. Its actual statement, noise normalization, and information definition were read in the main TeX at the user-pinned OpenAI revision. It covers every finite cube dimension and every soft kernel, including biased kernels and endpoints. I290's passage from this theorem to non-strict Gaussian contraction is a deduction, independently checked in Section 2 here. The additional classical identity is the NIST DLMF coth partial-fraction formula; the displayed product and partial fraction were independently read. No LSI, EPI, posterior Poincare inequality, or information-trajectory analyticity is used.

The I295 rearrangement/compactness deduction is considered separately in Section 9. Its primary Borell source was inspected at the operative statement and proof scopes. The rest of I290/I131's global cube chain is not promoted to an independently proved theorem by this review.

## 2. I290's actual non-strict Gaussian interface

The relevant passage is I290 Section 5, particularly line 292, and its I295 restatement in Section 6.1. A joint weak CLT by itself would not prove conditional entropy convergence. The conditional replacement argument supplied there does.

First fix a bounded smooth scalar v:R->[-1,1] with bounded derivatives through order three. On a cube of M fair bits write S_M(X)=M^{-1/2} sum_i X_i and u_M(X)=v(S_M(X)). At noise correlation r, condition on the *entire* output vector Y=y. The input bits are conditionally independent, with

    E[X_i|Y=y]=r y_i,
    Var(X_i|Y=y)=1-r^2.

Put xi_i=(X_i-r y_i)/sqrt(M). Each is conditionally centered, bounded in absolute value by 2/sqrt(M), and has conditional variance (1-r^2)/M. Replace these variables successively by independent centered Gaussians with that same variance. Taylor expansion through degree two for v, about the sum of all other terms, cancels the first two moments. Its third-order remainder gives

    sup_y |T_r u_M(y)-Q_r v(S_M(y))|
       <= C_r ||v'''||_infinity M^{-1/2}.

The conditional centering term r S_M(y) is arbitrary, but the derivative bound is uniform over it. The third absolute moments of both the bounded variables and their Gaussian replacements are O_r(M^{-3/2}); summing M errors proves the displayed bound. This is exactly the conditional-mean convergence needed, not conditioning a limiting weak joint law.

Ordinary scalar CLT and bounded continuous convergence give the input mean and entropy limits. The function Q_r v is bounded continuous. If omega_psi is the modulus of continuity of psi on [-1,1], the uniform conditional-mean error epsilon_M gives

    |E psi(T_r u_M(Y))-E psi(Q_r v(S_M(Y)))|
       <= omega_psi(epsilon_M)->0.

The second term tends to E_gamma psi(Q_r v). Noise preserves the mean, and the mean converges to E_gamma v. Thus

    I(u_M)->I(v),  I(T_r u_M)->I(Q_r v).

The stipulated cube theorem and continuity of f_r on [0,L] therefore yield I(Q_r v)<=f_r(I(v)). The same replacement works in every *fixed* Gaussian dimension, with independent blocks and a finite dimension-dependent Taylor constant. No uniform growing-dimension conditional CLT is needed for the present scalar theorem.

For a general measurable bounded w one can take v_j=Q_{t_j}w with t_j increasing to 1. The Gaussian kernel gives bounded smooth derivatives of every fixed order at each t_j<1; its Hermite multipliers and dominated convergence of squared Hermite coefficients give v_j->w in L2(gamma). Q_r is an L2 contraction. On [-1,1], L2 convergence implies convergence of entropy expectations by uniform continuity of psi and a split at |v_j-w|<=delta; means converge too. Passing to the limit proves

    I(Q_r w)<=f_r(I(w))                         (N)

for every measurable bounded scalar kernel. This validates the actual I290 interface needed by G for *every* compact perturbation and translation below. It does not assume I290's unpaid strict gap.

## 3. Audit of the scalar calculation

Fix a,r in (0,1), and set

    k=r V(ra)/V(a),  b=exp(psi(a))-1,
    M(a)=[a/(1-a^2)-V(a)]/[a/(1-a^2)+V(a)].

Here 0<b<1 and 0<k<r^2<1: V(z)/z increases strictly with z>0, as its positive series shows. In particular the later use of 1-k as a positive coefficient is justified.

### 3.1 b>M(a)

Since 1+M(a)=2a/[a+(1-a^2)V(a)], this is equivalent to K(a)>0, where

    K(a)=psi(a)+log[a+(1-a^2)V(a)]-log(2a).

With B(a)=a+(1-a^2)V(a), one has B'=2-2aV(a), psi'=V, and hence exactly

    K'(a)=[1-V(a)/a+(1-a^2)V(a)^2]/B(a).

No factor a or 1-a^2 is missing. B is positive. K has continuous endpoint limits zero: at zero B=2a+O(a^3) and psi(a)=O(a^2); at one (1-a^2)V(a)->0, B->1 and psi(a)->log 2.

Write a=tanh t, t>0. The numerator is

    1-t coth t+t^2 sech(t)^2.

[NIST DLMF equation 4.36.3](https://dlmf.nist.gov/4.36#E3), on the positive real axis, implies

    R(t):=(t coth t-1)/(t^2 sech(t)^2)
         =2 sum_{n>=1} cosh(t)^2/(t^2+pi^2 n^2).

This formula is locally uniformly convergent; the terms and their derivatives on any bounded positive interval are O(n^{-2}). Each summand increases strictly, since its logarithmic derivative is

    2[tanh t-t/(t^2+pi^2 n^2)]>0.

For completeness, (1+t^2)sinh t-t cosh t is zero at zero and has derivative t sinh t+t^2 cosh t>0. Thus tanh t>t/(1+t^2)>t/(t^2+pi^2 n^2) for t>0. The ordinary expansions of sinh and cosh give R(0+)=1/3; the first summand already tends to infinity as t->infinity. Consequently the continuous strictly increasing R crosses 1 exactly once. The numerator of K' is t^2 sech(t)^2(1-R(t)), so K strictly increases and then strictly decreases. Its two zero endpoint limits force K>0 everywhere inside. This proves b>M(a), including the strict sign near a=1.

The [product in DLMF 4.36.1](https://dlmf.nist.gov/4.36#E1) also yields the partial fraction by logarithmic differentiation, justified locally by sum n^{-2}<infinity. The review does not require treating that differentiation as an unverified identity.

### 3.2 The series quotient and the x factor

For 0<z<1, direct expansion yields

    M(z)/z^2 = [sum_{j>=0} A_j z^(2j)]/[sum_{j>=0} B_j z^(2j)],
    A_j=(2j+2)/(2j+3),  B_j=(2j+2)/(2j+1).

The coefficient ratios A_j/B_j=(2j+1)/(2j+3) increase strictly. To verify the quotient rule rather than invoke a named series lemma, put s=z^2. Its derivative numerator, paired over j>i, is

    sum_{j>i} (j-i)(A_j B_i-A_i B_j)s^(i+j-1)>0.

The double series and its derivative converge absolutely on compact subintervals of s<1. Already i=0,j=1 gives strict positivity. Thus M(z)/z^2 increases strictly.

Now set F(x)=V(a sqrt(x))/(a sqrt(x)) and z=a sqrt(x). Direct differentiation gives

    F'(x)=[z V'(z)-V(z)]/(2xz),
    F(x)+xF'(x)=[V(z)+zV'(z)]/(2z),
    F'(x)/(F(x)+xF'(x))=M(z)/x.

The denominator x is required and is correctly present in I300. The series monotonicity gives M(a sqrt(x))/x<=M(a) for 0<x<=1. Thus

    d[(1-bx)F(x)]/dx
      =(F+xF') [M(a sqrt(x))/x-b]<0.

Evaluating at r^2<1 and at 1 proves

    (1-br^2)V(ra)/(ra)>(1-b)V(a)/a,
    k>r^2(1-b)/(1-r^2 b).                      (S)

All denominators are positive. No amplitude restriction remains.

### 3.3 The curve's derivatives

At J=psi(a), differentiation gives f_r'(J)=k. Put H(a)=aV'(a)/V(a). With a=tanh t, H(a)=sinh(2t)/(2t), a strictly increasing function of a: z cosh z-sinh z has derivative z sinh z>0. Therefore

    d(log k)/da=[H(ra)-H(a)]/a<0,
    f_r''(psi(a))=(dk/da)/V(a)<0.

This proves increasing, strictly concave f_r on the entire open information interval, with the exact derivative used in the variation.

## 4. Biased binary likelihood ratios and Jensen

Let m=Ew, v=Var(w), and q=v/(1-m^2). Positive information implies |m|<1. Boundedness gives 0<q<=1. On the joint law of a Gaussian Z and a sign B with conditional mean w(Z), the density relative to P_B tensor gamma is

    R(s,z)=(1+s w(z))/(1+s m),  s in {-1,1}.

The marginal probabilities are (1+s m)/2. Each product-measure conditional density integrates to 1, and E_product R=1. Moreover

    E_product R^2
      =1+(v/2)[1/(1+m)+1/(1-m)]
      =1+q.

The joint expectation of R equals this product expectation of R^2. Direct calculation of the relative entropy gives I(w)=E_joint log R. For endpoints R can be zero on a product-measure set, but that set has joint measure zero; R log R extends continuously there. R is bounded for the fixed interior m, so all these quantities are finite. Jensen under the *joint* probability measure gives

    I(w)<=log E_joint R=log(1+q),
    q>=exp(I(w))-1.                            (R)

There is no normalization by a fair sign and no hidden m=0 hypothesis. If I(w)=psi(a), the lower bound is exactly q>=b.

## 5. Prior smoothing: all endpoint and tail interchanges paid

Take w=Q_tau u, 0<tau<1, with nonconstant u:R->[-1,1]. Let sigma=sqrt(1-tau^2), g_s=1+s u and A_s=1+s w for s=+1,-1. Neither g_s is zero almost everywhere, since that would make u a constant endpoint. For each sign choose R_s<infinity with delta_s=int_{-R_s}^{R_s} g_s(y)dy>0. The Gaussian convolution then gives

    A_s(x)>=delta_s/(sigma sqrt(2pi))
              exp[-(R_s+tau|x|)^2/(2sigma^2)]
           >=c_s exp(-C_s x^2)>0.

Also A_s<=2. Thus w(x) is strictly interior for every finite x, and

    |V(w(x))|<=C(1+x^2).

Differentiating the Gaussian kernel shows that every ordinary derivative of w is bounded: the nth derivative is a fixed tau,sigma-dependent constant times E[H_n(Z)u(tau x+sigma Z)]. All these statements also apply to h=Q_r w=Q_{r tau}u.

The score formula, with no derivative of u required, is

    A_s'(x)=(tau/sigma) E[Z g_s(tau x+sigma Z)].

Weighted Cauchy-Schwarz gives

    A_s'^2/A_s <= (tau^2/sigma^2) E[Z^2 g_s(tau x+sigma Z)].

Averaging the two signs gives the exact pointwise bound

    w'^2/(1-w^2)=0.5 sum_s A_s'^2/A_s
                <=tau^2/(1-tau^2).             (F)

In particular D=E w'^2/(1-w^2) is finite. It is positive whenever w is nonconstant, since D=0 would imply w'=0 everywhere by continuity.

For the additional logarithmic derivative estimate, the tilted standard Gaussian density is g_s(tau x+sigma z)/A_s(x). Its relative entropy is at most log(2/A_s(x)), because this bounds its log density on its support. For any real lambda, the elementary Gaussian variational inequality gives

    lambda E_tilt Z-lambda^2/2<=Ent_gamma(tilt).

One can prove this by nonnegativity of relative entropy against the normalized density exp(lambda z-lambda^2/2); all moments exist since the tilt is bounded for fixed x. Optimizing lambda yields

    |E_tilt Z|^2<=2 Ent_gamma(tilt)<=2log(2/A_s(x)).

The preceding Gaussian lower bound implies

    |(log A_s)'(x)|<=C(1+|x|),
    |d[V(w(x))]/dx|<=C(1+|x|).                 (P)

This last derivative is w'/(1-w^2), not the bare value V'(w). Claims about the latter alone would be false as a tail domination argument; I300 uses the composed derivative correctly. Together (F), (P), bounded w'', and quadratic V(w) give all required Gaussian integrability. Constants depend on the fixed input and smoothing parameters; no uniform bound over inputs is necessary for excluding an individual equality case.

## 6. Euler equation and differentiated energy identity

Assume a smoothed w has positive information J<L and equality in (N). Set h=Q_r w, m=Ew, k=f_r'(J). The functional G(v)=f_r(I(v))-I(Q_r v) is globally nonnegative on all bounded kernels by Section 2, and G(w)=0.

For phi in C_c^infinity(R), continuity and strict interiority of w on its compact support give |phi|<=C(1+w) and |phi|<=C(1-w) everywhere. Hence w+epsilon phi is admissible for both signs of small epsilon. Importantly,

    |Q_r phi|<=C Q_r(1+s w)=C(1+s h)

for both signs, so the output perturbation cannot cross an endpoint either. It remains a uniformly comparable distance from each output endpoint for small epsilon. Its entropy derivative is dominated by a bounded multiple of 1+|V(h)|, which is integrable by Section 5. The compact input part and interior mean cause no difficulty. Its information stays in (0,L) for small epsilon by continuity.

The first variation therefore is exactly

    0=E phi [k V(w)+(1-k)V(m)-Q_r V(h)].

Self-adjointness is justified by quadratic growth of V(h) and bounded compact phi. Thus the bracket vanishes gamma-almost everywhere. All its terms are continuous, so the identity is pointwise:

    Q_r V(h)=k V(w)+(1-k)V(m).                 (E)

No information or mean constraint is imposed on the perturbation, so there is no unspecified Lagrange multiplier. The constant term is forced by differentiating the two mean entropies.

By (P), (V(h))' has at most linear growth. Differentiation under the Gaussian convolution is legitimate, uniformly on compact x sets. Since h'=r Q_r w', differentiating (E) gives

    r^2 Q_r[(Q_r w')/(1-h^2)]=k w'/(1-w^2).

Multiply by w' and integrate. The inside function (Q_r w')/(1-h^2)=(V(h))'/r has linear growth, and w' is bounded. Absolute Fubini and self-adjointness apply, giving

    r^2 E[(Q_r w')^2/(1-h^2)]=k D.             (D)

The r^2 is correct: one factor comes from differentiating Q_r, the other from h'=r Q_r w'. Its left integral is finite also directly from the Fisher bound for h, after dividing by r^2.

## 7. Exact translation second variation and contradiction

The admissible path is w_c(x)=w(x+c); it stays in [-1,1] without clipping. There is a particularly useful exact output identity:

    Q_r w_c(x)=h(x+c/r).

Thus its first and second parameter derivatives at zero are Q_r w' and Q_r w'', respectively; they are h'/r and h''/r^2, not h' and h''.

For translations in a bounded c interval, (F), quadratic V(w), and bounded w'' dominate the first two input entropy chain-rule derivatives by C(1+x^2). The analogous output bounds hold using h(x+c/r). Therefore differentiating the entropy expectations twice is legitimate and continuous in c. The mean and its derivatives are bounded, and m stays interior near zero. Put

    A=E[(V(w)-V(m))w'],  m'=Ew'.

At zero the exact chain rule gives

    I(w_c)'=A,
    I(w_c)''=D+E[(V(w)-V(m))w'']-(m')^2/(1-m^2).

The output second derivative has E[(Q_r w')^2/(1-h^2)] in place of D and E[(V(h)-V(m))Q_r w''] for the linear term. The Euler identity cancels the two linear w'' terms, by self-adjointness; here V(h) has quadratic growth and w'' is bounded. Consequently

    G''(0)=kD+f_r''(J)A^2
            -E[(Q_r w')^2/(1-h^2)]
            +(1-k)(m')^2/(1-m^2).

This agrees with I300 exactly. The positive sign on the final mean term is essential. Independently, Gaussian change of variables gives, for any bounded integrand T,

    E T(Z+c)=E[T(Z) exp(c Z-c^2/2)].

Its first two derivatives at zero are E[Z T(Z)] and E[(Z^2-1)T(Z)]. Applied to T=psi(w) and T=w, these justify translation differentiability without any initial endpoint regularity claim. The chain-rule bounds above prove that these derivatives agree with the displayed expressions. Applying the same fact to psi(h) with c/r gives the matching output derivatives and factors. There is no discrepancy between the two methods.

Using (D), f_r''<0, and Cauchy-Schwarz,

    (Ew')^2 <= D E(1-w^2)=D(1-m^2)(1-q),

so, because 1-k>0,

    G''(0)<=D[k(1-r^{-2})+(1-k)(1-q)]
           <=D[k(1-r^{-2})+(1-k)(1-b)].

The last coefficient is exactly

    (1-b)-k(1-r^2 b)/r^2<0

by (S). Since D>0, G''(0)<0, contradicting that G(w_c)>=0=G(w_0). This excludes equality for every nonconstant positively smoothed scalar kernel at every open information/correlation pair.

## 8. Removal of prior smoothing

Suppose a general measurable w with J=I(w) in (0,L) attained equality at r. Choose r<tau<1 and put s=r/tau. Non-strict contraction gives

    I(Q_r w)<=f_s(I(Q_tau w))<=f_s(f_tau(J))=f_r(J).

The final identity follows immediately from the nonnegative inverse branch of psi. Strict monotonicity of f_s forces equality in both inequalities. Furthermore I(Q_tau w)>0: otherwise the first upper bound is f_s(0)=0, contradicting f_r(J)>0. Also I(Q_tau w)<=f_tau(J)<L. Thus the smoothed w_1=Q_tau w is nonconstant and within the exact range of Section 7. Equality at correlation s is impossible. This proves U300 for all measurable kernels without an analytic continuation premise. OU injectivity can also prove positive smoothed information, but the endpoint equality already suffices.

## 9. Gaussian compact-rectangle consequence and cube scope limit

The relevant I295 operations are Sections 2.2 and 6.1, not its restricted EPI comparison. The law-preserving scalar rearrangement is sound at its stated bias and endpoint scope. To check its interface independently, let f=(1+v)/2 and let f* be its increasing Gaussian quantile. Borell's two-set inequality at positive correlation bounds, for every output set A of measure p, the integral int_A Q_r f by the integral of Q_r f* over the upper ray A* of measure p, after layer cake over {f>t}. All rearranged input rays are nested level sets of this same quantile function, so no incompatible optimizing sets are chosen. Q_r f* is increasing. Taking largest-p integrals and then sup_p[M(p)-cp] bounds every stop-loss expectation. Equal means and piecewise-linear convex approximation therefore give convex order, hence

    I(v*)=I(v),  I(Q_r v)<=I(Q_r v*).

This verifies R295 from the primary two-set inequality, including atoms and empty/full level sets. The [primary Mossel–Neeman statement and complete Section 2 reproof](https://arxiv.org/html/1210.4126v3) were read. Independently differentiating its J Hessian gives J_pp=-r d/phi(alpha)^2, J_qq=-r d/phi(beta)^2, and J_pq=d/[phi(alpha)phi(beta)], where d is the bivariate Gaussian density at (alpha,beta). The joint OU generator then gives the nonnegative derivative r E[d |grad Phi^{-1}(f_t)-grad Phi^{-1}(g_t)|^2]. Interior regularization and bounded-continuous limits include indicators and endpoints. This check avoids relying on the typographical swaps present in the source's intermediate formulas. Its equality classification is not needed for U300.

Let M be the class of nondecreasing [-1,1]-valued scalar functions modulo gamma-null sets. Rational diagonal selection and monotone extension give convergence outside the countably many discontinuities of a bounded monotone limit. Dominated convergence gives L2(gamma) convergence, so M is compact. On a fixed rectangle 0<b_0<=b_1<1 and 0<r_0<=r_1<1, the set

    K={(w,b,r):w in M, b in [b_0,b_1], r in [r_0,r_1],
                    I(w)=psi(b)}

is compact and nonempty (w=b sign(x) works). I is continuous on bounded L2 kernels. Joint continuity of (w,r)->Q_r w follows by contraction plus Hermite expansion of the fixed limit function. Thus the continuous deficit f_r(I(w))-I(Q_r w) has a strictly positive minimum on K by U300. R295 transfers that minimum to every finite Gaussian dimension. This validates the qualitative full compact-rectangle Gaussian gap G290. It supplies no rate, effective constant, or uniform gap as a parameter approaches 0 or 1.

For the proposed unrestricted cube S128 conclusion, the exact remaining independent proof gate is the old cube chain: I290's J290/M290/P290 marked joining analysis, B290 marked-singleton entrance, D290 compression reduction, and T290 diffuse transfer, together with I128's ODE/backward budget identities and I131's quantitative compression/local bridges at their exact contracts. I290 was read completely for context and its conditional-mean interface was proved here; its other component assertions were not each independently re-proved against all source contracts. I295's complete restricted theorem and I131's local estimates likewise do not receive a new global proof gate from this review. Consequently this review validates U300, the needed non-strict Gaussian interface, and the R295/Helly implication to G290; **full S128 remains a downstream conditional consequence of the older chain**, not a separately passed theorem here.

## 10. Objections, repairs, and contribution limits

No substantive objection survives. The suspected x factor, binary output bias, mean coefficient, correlation factors, output perturbation admissibility, and arbitrary endpoint tails all check. Sections 5–7 supply explicit domination and comparison details for claims already made in the parent proof. These are explanatory expansions, not repairs; neither the theorem nor its assumptions are modified. There is no counterexample or unresolved step within U300 under the stipulated pinned cube theorem.

This review offers no acceptance nomination, contribution validation, worldwide novelty claim, literature exhaustion claim, or change to the accepted count. The classical series, likelihood-ratio Jensen, Gaussian smoothing, variational entropy bound, Borell rearrangement and Helly compactness are credited at their actual scopes. The parent-authored translation argument is mathematically validated here; a separate contribution gate and an independent audit of the full cube chain remain separate tasks. No numerical scan, subagent, live sibling read, shared-index edit, staging, commit, or publication was performed.
