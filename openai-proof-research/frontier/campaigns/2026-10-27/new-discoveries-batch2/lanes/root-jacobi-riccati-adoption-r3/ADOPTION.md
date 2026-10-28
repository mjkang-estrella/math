# Jacobi Riccati route: valid ordinary partial result, no credit

Root read the completed Sol report, check program, current-registry screen, and
actual cached primary text (Definition 2.1, Computational observation 3.1,
Theorem 1.4 and Remark 3.8). Root also read the completed child thread. This
adoption is dated 2026-10-28. The full shifted denominator law remains open.
Count stays 2/30 additional, 32/60; no Lean, manuscript or acceptance is implied.

## Ordinary deduction assessed

Root independently checked the algebraic chain in discovery.md:

- On x=(1+it)/2, y=(1-i/t)/2, 2xy=x+y and D=-(1+t^2)d/dt=2i delta.
  Homogeneity and the coefficient recurrence for P_l give
  D^2 C_s+2is D C_s+2i D C_(s+1)-V C_s=0, with
  V=u(1+t^2)+v(1+t^-2). The mixed operator term vanishes on this curve.
- Z e_s=e_(s-1)+s e_s gives the formal equation
  D^2 F+2iZ DF-VF=0. Coefficientwise summation is finite; no analytic phase
  identity, convergence or unproved asymptotic identification is needed.
- The unique derivative of log F has coefficients s_1=V and
  s_(n+1)=-D s_n-sum_(a+b=n) s_a s_b in powers of (2iZ)^-1.
  Their integrality, divisibility by 1+t^2, parity and parameter-degree bound
  follow by induction. For odd n, division by 1+t^2 leaves even Laurent powers,
  so the unique odd primitive has only odd rational denominators.
- The imaginary part of each literal L_n is odd in t. For even n its derivative
  is zero, hence it vanishes. This repairs the earlier parity gap using the
  actual differential equation. Parameter degrees beyond ceil(n/2) likewise
  have derivative zero; evaluation at t=i gives x=y=0 and kills constants.
- The highest homogeneous part of s_(2r-1) is
  (-1)^(r-1) Catalan_(r-1) V^r: only odd/odd products contribute to degree r.
  Its pure-u primitive gives
  [u^r]kappa_r=Catalan_(r-1) I_r/2^(4r-2)
  =2 binom(2r,r) I_r/((2r-1)16^r).
  This proves the literal source's observation (14) at all orders as an
  ordinary partial deduction. Source Theorem 1.4 gives v2(I_r)=r-1+v2(r);
  v2(Catalan_(r-1))=s2(r)-1. Thus the coefficient valuation is exactly
  -2r-v2((r-1)!). These published valuation facts are uncredited dependencies.

## Remaining gap

Let J be evaluation at t=1 of the unique odd D-primitive. Still unproved:

    (r-1)! J(s_(2r-1)) in 2^(2r-2) Z_(2)[u,v] for every r>=1.

The top coefficient supplies attainment only. It does not bound lower
homogeneous pieces. The stronger degree-specific assertion with (d-1)! instead
of (r-1)! is a conjectural sufficient target, not a proved equivalence.
Termwise divisibility before midpoint evaluation fails already for t+t^3/3;
the unrestricted shifted-binomial-moment shortcut also fails (464/315).

## Verification and limits

Root reran an exact byte-copy of the worker's check.py in this own lane, without
editing the completed worker. PASS: source-vs-Riccati n<=9, curve equation s<=4,
generic operator identity, recurrence/top formula/degree-specific guess r<=8,
and both shortcut falsifiers. The copy and actual generated checks.json are
retained. This is a replay of worker diagnostics, not an independent checker or
a proof of the unbounded assertion; the root's ordinary reasoning is above.

The worker's bounded current-registry search found no relevant counterpart.
Root read its recorded scope and actual source snippets, but did not repeat all
network retrievals. No final novelty PASS or global-absence claim is issued.
MathDB 391922 is the already resolved original-variable question, not this
shifted target. No standalone credit is sought for the top coefficient or tools.

## Next research lead (unproved)

The midpoint-adapted Laurent coordinates z=t+t^-1, y=t-t^-1 satisfy
z^2-y^2=4, Dz=-zy, Dy=-z^2, and
V=((u+v)z^2+(u-v)zy)/2. At t=1, z=2 and y=0.
These exact identities may expose cancellation hidden by termwise t-power
valuations. They do not by themselves prove the required filtered-ring bound;
primitive denominators and reductions by z^2-y^2=4 must be controlled.
