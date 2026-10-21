# Independent operative contribution reduction

Working derivation for T360S147 at the unchanged frozen statement. Contribution is conditional on correctness; this file assigns no correctness verdict. The final contribution disposition is in REVIEW.md when sealed.

## What is supplied

Source360's foundation supplies the full ordinary-subgradient support, lifted convex sections, intermediate graph homeomorphism and geometry-only C1,1 intermediate potential. Its Holder companion supplies all-point singleton endpoint contacts and reverse contacts. The lifted zero section plus its diameter inequality makes the log singleton too. Thus the source graph has a common midpoint parameter z and two Lipschitz endpoint homeomorphisms X,Y with T=Y composed with X inverse. There is no endpoint inverse Sobolev assumption here.

At t=1/2 write w=Q_tu and, at parameter differentiability points,

    P=Dzz(c(X,z)/t)-D2w >=0,
    Q=D2w+Dzz(c(z,Y)/(1-t)) >=0.

These inequalities are just the source's two touching supports. Differentiating the touching first-derivative identities gives

    DX=L_X P, DY=L_Y Q,
    L_X=-(D_zx c_t)^(-1), L_Y=-(D_zy c_(1-t))^(-1).

The halves lie in a compact subset of the smooth nondegenerate cost region, so these smooth factors and their inverses are uniformly bounded by geometry. Source360's exact fixed-join Jacobi factorization says D=P+Q is singular precisely at full focality, including conjugacy. The geometric identification is an input already paid, not a new operation in this nominee.

## The full weighted derivative, not merely an a.e. chain rule

For an orientation-preserving Lipschitz homeomorphism X:V->U and Lipschitz scalar Z on V, set f=Z composed with X inverse. Let A=DX. For a test phi compactly supported in U, injective area formula and A adj(A)=det(A)I give

    integral f partial_j(phi)
      = integral Z (partial_j phi)(X) det A
      = integral Z sum_k cof(A)_(jk) partial_k(phi composed with X).

Distributional rowwise Piola, valid for Lipschitz X by local convolution and convergence of the polynomial minors, gives

    integral f partial_j(phi)
      = -integral (phi composed with X) (DZ adj(DX))_j.

The nonsmooth test Z(phi composed with X) is justified by W1,1 approximation on its compact parameter support; the cofactor is bounded and divergence-free. Consequently

    D(Z composed with X inverse)=X_#(DZ adj(DX) dz).

This argument already proves BV and identifies its entire derivative measure. A constant orientation sign is inserted on a reversing chart. It does not delete the critical locus det DX=0. The formula for vector Z holds componentwise. It is also the mixed horizontal/vertical minor formula obtained by applying Stokes to phi(x)y_alpha dx_1 wedge ... omit dx_j ... wedge dx_n on the Lipschitz parameterized graph (X,Y). This is exactly the graph-current operation in Alberti--Ambrosio Proposition5.1/proof (5.2)--(5.5), using their Proposition4.2 area/minor formula. In the present parameterization that mixed minor is DY adj(DX). This is classical null-Lagrangian calculus, not a new inverse chain rule.

## Exact focal cancellation

If D=P+Q is singular, choose a!=0 in its kernel. Positivity gives Pa=Qa=0. If rank P<=n-2 then adj(P)=0. Otherwise rank P=n-1 and im adj(P)=ker P=span(a), which Q annihilates. Hence Q adj(P)=0 in every dimension n>=2, with no commutativity assumption. Multiplication of adjugates in the correct reversed order yields

    DY adj(DX)=L_Y Q adj(P) adj(L_X)=0.

An equivalent exact check: the common vector a lies in both ker DX and ker DY, so the stacked graph derivative (DX,DY) has rank<n and all of its n-minors vanish. This is a derivative-kernel computation, not an inference from the size or codimension of an exceptional image. Its particular mixed minors are precisely the weights in the preceding distribution formula.

If E is the closed endpoint focal set, restriction commutes with pushforward by the homeomorphism X. Thus

    |D(Y composed with X inverse)|(E)=0.

The nondifferentiable parameter null set contributes nothing to the parameter Lebesgue-density measure. Also det DX=0 a.e. on X inverse(E), so area formula shows vol(E)=0; this latter fact alone would not suffice for removal.

## Nonfocal part and the whole frozen conclusion

On the open complement of E, singleton logs plus nonconjugacy make the true cost smooth and nondegenerate in small product patches. Reverse contact uniqueness supplies strict c-convexity. Keeping the global dual data on a target patch retains every actual contact; its contact measure has bounds from lambda/Lambda and smooth coordinate volume factors. A small compact section gives the exact boundary localization used in DPF1211.2341v1, not a globally cost-convex coordinate-domain assumption. That theorem supplies local W2,1+kappa potentials, hence local W1,1 maps. No sum of degenerating DPF constants is required. The finite derivative measure is absolutely continuous on the open nonfocal part and zero on E, so is absolutely continuous globally.

In volume frames the cofactor C_X has norm at most Lip(X)^(n-1). With a fixed isometric embedding iota and Lip(X),Lip(Y)<=L_g,

    |D(iota composed with T)|(M)
      <= integral |d(iota composed with Y) C_X|
      <= sqrt(n) L_g^n vol_g(M).

Coordinate volume factors multiply the polynomial density; they cannot disturb its zero. Local orientation signs and the transformation law allow patching also on nonorientable M. Repeat with X,Y exchanged. The total bound is at most 2 sqrt(n) L_g^n vol_g(M), common to all allowed lambda,Lambda. This reduction retains the entire frozen dimension, density, focal, orientation and constant scope.

## What this comparison does not assert

It does not conclude that any Lipschitz X has Sobolev inverse. CHM and Hencl explicitly provide counterexamples and distinguish BV from W1,1. It does not apply finite-distortion inverse theorems to X without proving their hypotheses. It does not discard singular measure using CEMS a.e. cut avoidance or a.e. Jacobian information. It does not solve the old smooth cut-avoidance, stability, or bi-W1,2 approximation targets. All source geometry, DPF section regularity, graph-current/Piola calculus and old cofactor arguments receive operative credit.
