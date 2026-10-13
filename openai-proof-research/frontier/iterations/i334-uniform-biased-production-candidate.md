# I334 — uniform biased entropy production

2026-10-13. **Parent proof candidate, not independently reviewed or accepted.** The claim below is a proposed new quantitative consequence of the stipulated sharp binary-information manuscript. It is not obtained by applying a one-coordinate estimate to a general field. The full joining induction is supplied.

## 1. Claim and notation

Let psi(s)=((1+s)log(1+s)+(1-s)log(1-s))/2, L=log 2, H=L-psi, V=atanh, and define F(psi(s))=s atanh(s). For an interior-valued field u on a finite uniform cube, put

    m=Eu, I=Epsi(u)-psi(m),
    D=(1/4)sum_i E[(u-u^(i))(atanh(u)-atanh(u^(i)))].

There is an absolute c>0 such that, for every dimension and every such field,

    D >= F(I)+c m² I².                                      (BP)

Constants do not deteriorate as |m| tends to one. Endpoint-valued fields are included by the positive-time limit, with possibly infinite production. Constant fields have I=D=0.

The pinned manuscript is Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All its theorems are stipulated true. We use its scalar bounds, variance-refined one-bit inequality, exact cost optimizer, reserve joining theorem, and strict thinning derivative. New inequalities below upgrade its potential and explicitly pay the upgrade on every joining geometry.

## 2. Fixed positive constants and the new potential

The source gives, for 0<=I<L,

    F'(I)>=2,  F''(I)>=mu:=1/(2L²),
    F''(I)<=M/(L-I)²,  M=4L²/3,  delta0:=2-3M>0.

Its wall:rate-slope gives F''/F'<2 on [0,L/2]. Set

    eta=2-max_[0,L/2] F''/F'>0.

With S=F-2I, k0=L-1/2 and Xi(I)=(I-k0)S'(I)-S(I), the source proves Xi(L/2)>0 and Xi is increasing on [L/2,L). Put

    A=mu/2, B=delta0/8, C=4L²+3L/2,
    c=(1/2) min{mu/8, B/C, eta, Xi(L/2)/L²} >0.

Define G(m,I)=F(I)+c m² I² and P_m(I)=max{B_m(I),G(m,I)}, where B_m is the source's linear-reserve profile.

G is jointly convex for |m|<1, 0<=I<L. Indeed its Hessian entries are 2cI², 4cmI and F''+2cm². Its determinant is 2cI²(F''-6cm²)>=0, since c<=mu/8. The diagonal entries are nonnegative. This proves convexity on the full convex rectangle, hence also on the physical hypograph 0<=I<H(m).

The source's high-information calculation gives B_m(I)-F(I)>=m² Xi(I) for I>=L/2. Since Xi(I)>=Xi(L/2)>=c I², B_m>=G there. At m=0, B_0=F=G. Consequently any strict G-parent branch, G(m,I)>B_m(I), has I<L/2 and m!=0.

## 3. Quantitative common-output payment

Use the source thinning path from an interior ordered core (a_c,b_c), center x_c>=0, half-difference d_c>0 and core information J_c. Let sigma_c=1-x_c, and mix mass lambda on the core with mass 1-lambda at (1,1). Its parent center is x=1-lambda sigma_c. Let I=H(x)-lambda h_c, let nu be average child information, and J=I-nu. Here 0<lambda<=1 and d_c<sigma_c.

First retain the source's strict derivative margin. Write Delta_F(lambda)=F(I)-F(nu). Equations thinning:normalized-derivative through thinning:window-bound give

    lambda Delta_F' - Delta_F >= delta0 kappa(lambda),
    kappa(lambda)=-(1/2)log(1-lambda² d_c²/(1+x)²)
                  >=lambda² d_c²/8.

Integrating the derivative of Delta_F/lambda from lambda to 1, where Delta_F(1)=F(J_c), yields

    lambda F(J_c)-[F(I)-F(nu)]
        >= B lambda(1-lambda)d_c².                       (T)

The core cost obeys c_core>=alpha F(J_c/alpha), alpha=1-x_c², by source capacity:onebit. Write F(s)=mu s²/2+R(s), where R is convex and R(0)=0. Convexity implies alpha R(J_c/alpha)>=R(J_c), so

    c_core-F(J_c)>=A (1/alpha-1)J_c²
                    >=A x_c² J_c².                      (C)

We now bound the desired correction, rather than discarding the margin. Let p_c=sigma_c/2 and let h_bin be binary entropy. The flag information is

    I=lambda J_c+E_lambda,
    E_lambda=h_bin(lambda p_c)-lambda h_bin(p_c).

For g(t)=-(1-t)log(1-t), one has -2<=g''<=-1 on [0,1/2]. Convexity of g(t)+t² gives

    0<=g(lambda p_c)-lambda g(p_c)
       <=lambda(1-lambda)p_c².

Separating -t log t and using p_c<=1/2 and 1-lambda<=log(1/lambda) gives

    0<=E_lambda<=(3/4)lambda sigma_c log(1/lambda).

The channel chain rule, or data processing after forgetting the independent flag, gives J<=lambda J_c. The source posterior identity and psi(s)<=L s² give

    J_c<=L d_c²/[sigma_c(1+x_c)],
    sigma_c J_c<=L d_c²,  J_c²<=L² d_c².

Since x=x_c+(1-lambda)sigma_c, x²<=2x_c²+2(1-lambda)². Therefore

    x²(I²-nu²)
      =x² J(2I-J)
      <=4lambda x_c²J_c²+C lambda(1-lambda)d_c².           (Q)

For clarity: use J<=lambda J_c and I<=lambda J_c+(3/4)lambda sigma_c log(1/lambda). Their product contributes 2lambda² x²J_c² and (3/2)lambda² x²sigma_cJ_c log(1/lambda). Bound the first by 4lambda x_c²J_c²+4L²lambda(1-lambda)d_c², and the second by (3L/2)lambda(1-lambda)d_c², using lambda log(1/lambda)<=1-lambda.

Combining (T), (C), (Q), and c<=A/4 and c<=B/C, the exact canonical cost lambda c_core satisfies

    lambda c_core >= G(x,I)-G(x,nu).                    (GCP)

This applies to every core mass, including lambda=1. In particular it strengthens source thinning:high-value on the entire one-positive-corner branch, not just its capacity endpoint.

## 4. Reflected cores: monotonicity of the upgraded demand

Fix d,e and a physical m>0 with I=H(m)-e<=L/2, j=[H(m+d)+H(m-d)]/2-e, and J=I-j>0. Put W=V(m), and Q0=[V(m+d)+V(m-d)]/2. The source proves

    Q0/W >=exp(2J),
    F'(I)/F'(j)<=exp((2-eta)J).

The second follows by integrating the definition of eta. Thus

    Q0 F'(j)-W F'(I)>=2 eta W J.

Differentiating the new demand at fixed d,e gives

    d/dm [G(m,I)-G(m,j)]
      = Q0 F'(j)-W F'(I)
        +2cm(I²-j²)+2cm²(jQ0-IW).

Since Q0>=W and j>=0, jQ0-IW>=-JW. The last two terms are therefore at least -2cWJ. As c<eta, the derivative is positive.

For the source's reflected optimizer, d=kr, e=kH(r), cost=dV(r), and 0<m<=ell:=1-k. Increasing m to ell preserves d,e,cost and decreases I, so I remains below L/2. The upgraded demand is increasing, and at ell the geometry is the one-positive-corner transition. Apply (GCP) there and compare back. Hence the exact cost also pays G(m,I)-G(m,j) on every reflected strict-parent branch. Zero length of this interval needs only the endpoint inequality.

## 5. Full joining inequality and dimension induction

Let the two arbitrary original child fields have means a,b and entropies e_a,e_b>0. Set m=(a+b)/2, e=(e_a+e_b)/2, I=H(m)-e and I_a=H(a)-e_a, I_b=H(b)-e_b. Their average information is j=[H(a)+H(b)]/2-e. Reflect/swap to m>=0,d=|a-b|/2 if necessary.

If P_m(I)=B_m(I), source reserve:joining gives

    E c(A,B)>=P_m(I)-[P_a(I_a)+P_b(I_b)]/2,

because each child P dominates its reserve value.

Otherwise G(m,I)>B_m(I), so m>0 and I<L/2. If d=0, then I=j and joint convexity of G pays the inequality with nonnegative cost. If d>0, the source canonical:coverage and its two geometries identify the minimum K(m,d,e) of the joining cost while retaining the original means and average entropy. Sections 3 and 4 prove K>=G(m,I)-G(m,j). Joint convexity gives

    [P_a(I_a)+P_b(I_b)]/2
      >=[G(a,I_a)+G(b,I_b)]/2>=G(m,j).

Adding proves the same full joining inequality. Importantly the original individual child entropies were not replaced by canonical ones; only their average enters K, and their own values enter the convexity inequality.

Induct now on cube dimension, using the exact source production decomposition D(u)=[D(u_+)+D(u_-)]/2+E c(u_+,u_-). Constant fields have P_m(0)=0. The new joining inequality completes the induction and proves D>=P_m(I)>=F(I)+cm²I², which is (BP).

## 6. Consequence and limits

The candidate (BP) pays precisely the missing hypothesis in the parent I332 semigroup reduction. If it passes independent review, it supplies a uniform a^4 deficit for means bounded away from zero. Combining it with a fully validated all-kernel fixed-interior-mean small-information theorem would prove the complete S313 endpoint stability estimate. No such combination is accepted by this draft, and the production theorem and full endpoint package should count as one connected contribution rather than separate acceptances if nominated.

The new content is the quantitatively paid G(m,I) potential, including common-output slack and joint child pooling. All scalar estimates, exact optimizer existence, reserve joining and thinning machinery remain credited to the stipulated source. This is not a claim of world priority. No numerical scan or formal proof checker was used. The proof must be independently attacked before acceptance.
