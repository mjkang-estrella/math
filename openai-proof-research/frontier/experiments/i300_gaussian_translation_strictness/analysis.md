# I300 parent proposal: strict Gaussian contraction from translations

2026-10-13. **Unreviewed proposed proof.** No acceptance, priority or independent validation claim. This is a proposed replacement for the unpaid scalar strictness U295, not an alteration of frozen I295/I298/I299 inputs. All pinned OpenAI results remain stipulated. The deduction uses I295's scalar reduction and I290's non-strict Gaussian limit; neither internal deduction is an upstream stipulation.

## 1. Statement and notation

Let gamma be standard Gaussian probability on R and Q_r its OU noise operator, with correlation 0<r<1. Set

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    V(t)=atanh(t),
    I(w)=E psi(w)-psi(Ew),
    f_r(J)=psi(r psi^{-1}(J)).

The proposed scalar conclusion is

    I(Q_r w)<f_r(I(w))                         (U300)

for every measurable w:R->[-1,1] with 0<I(w)<log 2. This is all amplitudes and correlations in the open interval, not the restricted I295 rectangle.

The input non-strict inequality I(Q_r w)<=f_r(I(w)) is the Gaussian limit of pinned cube contraction, via I290's conditional block-sum approximation. Its proof, including conditional entropy convergence, must be reviewed separately. It is used for *all* perturbed kernels below.

## 2. Elementary scalar inequality required by the argument

For a,r in (0,1), put

    k=r V(ra)/V(a), b=exp(psi(a))-1.

The claimed strict inequality is

    k>r^2(1-b)/(1-r^2 b).                       (S)

Here 0<b<1. The following analytic proof is proposed; the identity and endpoint passages require independent checking.

First define

    M(a)=[a/(1-a^2)-V(a)]/[a/(1-a^2)+V(a)].

We claim b>M(a). This is equivalent to

    K(a):=psi(a)+log[a+(1-a^2)V(a)]-log(2a)>0.

K extends continuously to 0 and 1, with K(0)=K(1)=0. Differentiation gives, with a=tanh t,

    K'(a)=[1-V(a)/a+(1-a^2)V(a)^2]
               /[a+(1-a^2)V(a)],
    numerator=1-t coth(t)+t^2 sech(t)^2.

The numerator is positive and then negative, with exactly one sign change. One way to establish this is the classical partial-fraction identity

    (t coth(t)-1)/(t^2 sech(t)^2)
       =2 sum_{n>=1} cosh(t)^2/(t^2+pi^2 n^2).

Every summand is strictly increasing for t>0: its logarithmic derivative is 2[tanh t-t/(t^2+pi^2 n^2)]>0. The elementary bound tanh t>=t/(1+t^2) follows by differentiating (1+t^2)sinh t-t cosh t; its derivative is t sinh t+t^2 cosh t>0. The sum starts at 1/3 and diverges to infinity (already its first term does). Local uniform convergence justifies the identity and monotonicity. Thus K increases and then decreases to zero, and is positive inside. The partial-fraction identity can be obtained by logarithmically differentiating the product sinh t/t=product_{n>=1}(1+t^2/(pi^2 n^2)); it is classical and not a new theorem.

Second, M(z)/z^2 is strictly increasing for 0<z<1. Indeed it is the ratio of the two positive series

    sum_{j>=0} [(2j+2)/(2j+3)] z^(2j)
      / sum_{j>=0} [(2j+2)/(2j+1)] z^(2j).

The ratios of corresponding coefficients, (2j+1)/(2j+3), increase strictly. Differentiating the quotient and grouping indices j>i makes each paired term positive.

Put F(x)=V(a sqrt(x))/(a sqrt(x)), continuously extended at zero. Direct differentiation gives

    F'(x)/(F(x)+x F'(x))=M(a sqrt(x))/x<=M(a),

for 0<x<=1. Since b>M(a), the function (1-bx)F(x) has strictly negative derivative. Evaluating it at x=r^2 and x=1 yields

    (1-br^2) V(ra)/(ra)>(1-b)V(a)/a,

which is exactly (S).

Also f_r is strictly increasing and strictly concave on (0,log 2). Its derivative is k above; k decreases with a because a V'(a)/V(a)=sinh(2t)/(2t), t=V(a), increases strictly. Hence f_r''<0. These signs matter in the second variation.

## 3. A universal entropy/variance bound

Let m=Ew, v=E(w-m)^2, q=v/(1-m^2). Positive information implies |m|<1. Sample B in {-1,1} given Z with P(B=+1|Z)=(1+w(Z))/2. The density R of P_{B,Z} relative to P_B tensor gamma is

    R(b,z)=(1+b w(z))/(1+b m).

Thus

    I(w)=E_joint log R <=log E_joint R
          =log E_product R^2=log(1+q).          (R)

This is Jensen, not an imported sharp stability theorem. Consequently q>=exp(I(w))-1. The joint-density calculation must retain the output bias; assuming m=0 would lose the target scope.

## 4. Equality implies an Euler equation

First take w=Q_tau u for some 0<tau<1 and nonconstant bounded u. Then w is smooth, strictly between -1 and 1, and all its ordinary derivatives are bounded. Both 1+w and 1-w admit a lower bound c exp(-C x^2), by restricting the defining Gaussian integral to a fixed interval on which the corresponding input has positive mass. Therefore |V(w(x))|<=C(1+x^2); the same statements hold for Q_r w.

Assume equality I(Q_r w)=f_r(I(w)), and set a=psi^{-1}(I(w)), k=f_r'(I(w)). The functional

    G(v)=f_r(I(v))-I(Q_r v)

is nonnegative for all [-1,1]-valued kernels and zero at w. Every compactly supported smooth additive perturbation is admissible at small positive and negative parameter, since w is uniformly interior on its support. Its first variation vanishes. OU self-adjointness gives the pointwise Euler identity

    Q_r[V(Q_r w)]=k V(w)+(1-k)V(m).             (E)

This multiplier is fixed by the sharp curve. There is no extra free mean or information Lagrange multiplier, because G itself has a global minimum.

Write

    D=E[w'^2/(1-w^2)].

It is positive and finite. In fact Cauchy-Schwarz applied separately to the two smoothed sign densities gives the pointwise bound

    w'^2/(1-w^2)<=tau^2/(1-tau^2).

To see it, put A_±(x)=E[1±u(tau x+sqrt(1-tau^2)Z')]. Then A_±'=tau/sqrt(1-tau^2) E[Z'(1±u(...))], so A_±'^2/A_± is at most tau^2/(1-tau^2) E[Z'^2(1±u(...))]. Average the two signs.

Differentiating (E), using (Q_r h)'=r Q_r h', then multiplying by w' and integrating yields

    r^2 E[(Q_r w')^2/(1-(Q_r w)^2)]=kD.        (D)

All differentiations need justification at infinity. A proposed sufficient estimate is |(log A_±)'|<=C(1+|x|). The tilted standard Gaussian with density (1±u)/A_± has entropy at most log(2/A_±); the Gaussian variational bound on its mean gives |E_tilt Z'|^2<=2log(2/A_±). The preceding lower bound on A_± supplies the estimate. This also bounds V'(w)w' polynomially. It permits differentiation under Q_r and the self-adjoint interchange in (D); alternatively use truncation followed by the displayed Fisher bound.

## 5. Translation second variation contradicts equality

The path w_h(x)=w(x+h) remains in [-1,1] for every real h. Since G(w_h)>=0=G(w), its second derivative at zero is nonnegative. Let

    A=E[(V(w)-V(m))w'], m'=Ew'.

Using the first variation (E) to cancel the w'' term in the path derivative, the exact second variation is

    G''(0)=kD+f_r''(I(w)) A^2
       -E[(Q_r w')^2/(1-(Q_r w)^2)]
       +(1-k)(m')^2/(1-m^2).

The signs and factors here are critical. The output perturbation is Q_r w', whereas differentiating Q_r w spatially introduces an additional r. Substituting (D), concavity f_r''<0 and Cauchy-Schwarz gives

    0<=G''(0)
      <=D[k(1-r^(-2))+(1-k)(1-q)],              (T)

because

    (Ew')^2 <= E[w'^2/(1-w^2)] E(1-w^2)
             =D(1-m^2)(1-q).

By (R), q>=b=exp(psi(a))-1. By (S),

    (1-k)(1-b)-k(1-r^2)/r^2<0.

The right side of (T) is therefore strictly negative, contradicting D>0. This rules out equality for every positively smoothed nonconstant scalar kernel, without a monotonicity or balanced-output assumption.

The translation derivative is well-defined directly by Gaussian change of variables: E psi(w(Z+h)) and Ew(Z+h) have derivatives obtained by multiplying the bounded integrands by Gaussian Hermite polynomials. The alternative chain-rule expression above is integrable because the Fisher terms are bounded and V(w)w'' has polynomial growth. The corresponding output terms have the same properties. The Euler identity cancels the w'' contribution by self-adjointness and these integrability bounds.

## 6. Remove prior smoothing; prospective consequence

Suppose a general nonconstant w with 0<I(w)<log 2 had equality at correlation r. Choose tau in (r,1), and write r=s tau. Non-strict contraction twice gives

    I(Q_r w)<=f_s(I(Q_tau w))
       <=f_s(f_tau(I(w)))=f_r(I(w)).

Equality at the ends, strict monotonicity of f_s and the curve's semigroup identity force equality at both steps. But Q_tau w is a positively smoothed nonconstant kernel with positive information, contradicting Section 5. Hence U300 would hold for all measurable scalar kernels.

If verified, I295's law-preserving scalar rearrangement and compact monotone optimization turn U300 into the full dimension-independent Gaussian gap on every compact open parameter rectangle. I290's diffuse transfer, marked-singleton theorem and I131 compression/local estimates then give the unrestricted global S128 theorem. Those prior internal ingredients and this new argument must pass independent proof and contribution review before such a conclusion is accepted. No effective stability constant is claimed.

## 7. Evidence and next gate

This proposal was derived by the parent from a second-variation calculation. No numerical experiment or independent review has been performed. The elementary analytic inequalities are displayed in full precisely to expose possible sign or coefficient errors. The prior active reviews concern frozen S295, and are not silently redirected to this stronger proposal. Needed next: an independent adversarial proof review of Sections 2–6, then the full global chain and contribution assessment if it survives.

The initial external search returned Gaussian LSI references, including the primary Bobkov–Gozlan–Roberto–Samson article at https://doi.org/10.1016/j.jfa.2014.09.016 and Dolbeault et al. at https://arxiv.org/abs/2209.08651. Neither article was read or used as a theorem in this proof. The classical sinh product and coth partial-fraction formula were checked directly in the primary NIST DLMF reference, https://dlmf.nist.gov/4.36, equations 4.36.1 and 4.36.3. The complete 89-line browser rendering was read, including both displayed identities. The derivation above uses their standard local uniform convergence on the positive real axis. Source reading for prior Gaussian/cube operations remains in the completed I290/I295 records.
