# Frozen r229 statement: critical radial asymptotics and affine ball-volume growth

Let (F,P) be the specific normalized smooth positive radial solution in the dimension-ten Source353 manuscript at revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, constructed in Lemma `lem:local` and Proposition `prop:global`. Thus F(0)=P(0)=1, D²_x F(0)=I in R^9, and, writing y=F' and r=|x|,

    y^8 y' = r^8 F P^(−12/11),
    (y^8 P')' = −11 r^8 P^(−1/11),   F'=y.

Let u(x,t)=sqrt(F(|x|)^2+t^2) on R^9×R, and let g=(det D²u)^(−1/12)D²u be its Berwald–Blaschke metric, with the determinant and Hessian in the original affine coordinates (x,t). The source's global construction, pointwise positivity, smoothness and affine maximality are assumptions, not new conclusions of this statement.

For r>0 set A=rF'/F, B=rF''/F', C=−rP'/P and D=C/B. Then:

1. A,B,D are strictly increasing in r and converge respectively to 9/2,7/2,33/7. For tau=log r→+infinity,

       (9/2−A, 7/2−B, 33/7−D)
       = [15/(7tau)](1,1,110/147) + O(log(tau)/tau²).

   The error is in the ordinary Euclidean norm on R^3. There are constants cF,cP>0 such that

       F(r)=cF r^(9/2)(log r)^(−15/7)
             [1+O(log log r/log r)],
       P(r)=cP r^(−33/2)(log r)^(110/7)
             [1+O(log log r/log r)],
       (9/2)^9(7/2)cF^8 cP^(12/11)=1.

   All error constants concern this fixed normalized source solution; no uniform parameter-family bound is asserted.

2. The global coordinates (x,v), t=F(|x|)sinh v, give

       g=P^(1/11)[D²_xF+F dv²].

   Put Q(r)=F(r)P(r)^(1/11) and rho(r)=integral_0^r sqrt(P(s)^(1/11)F''(s)) ds. Then Q is strictly increasing for r>0, Q(0)=1, and rho maps [0,infinity) onto [0,infinity). In polar coordinates away from the central axis,

       g=d rho²+phi(rho)² g_S8+psi(rho)² dv²,
       phi²=QA,  psi²=Q,
       lim_(rho→infinity) phi²/rho²=9/14,
       lim_(rho→infinity) psi²/rho²=1/7.

   The tensor extends smoothly across the axis and is complete. Completeness is included as an accounted-for consequence, not the proposed distinct contribution.

3. Let p0 be the graph point above (x,t)=(0,0), and let Vol_g be Riemannian volume. Writing |S^8| for the area of the unit round eight-sphere,

       lim_(R→infinity) Vol_g(B_g(p0,R))/R^11
         = |S^8| (9/14)^4 /(55 sqrt(7)).

   The same limit holds for every fixed center p on the graph. This is the normalized metric just specified; the numerical coefficient is not asserted invariant under arbitrary ambient affine changes.

This entire statement is submitted as one prospective author-proof target. No correctness, contribution, acceptance or count is assigned. It is not a claim of worldwide priority, nor an assertion of a proper global tangent cone at infinity.
