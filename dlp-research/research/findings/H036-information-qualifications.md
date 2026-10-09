# H036 information/algebra proposals: accepted scope

Factory Fable5.1's independent report is terminal and retained raw. It fetched
no primary sources in this task. Root accepts two elementary lemmas after a
separate native Astra audit, not the report's broad closures or calibration.
No run, implementation or Lean infrastructure is admitted by these cards.

## Global polynomial-coefficient recurrence lemma

Let distinct primes p,q and a nonconstant q-periodic sequence W:Z->Fp be given.
For elliptic abscissae an explicit value must be assigned at infinity. Suppose
a nonzero tuple c_0,...,c_r in Fp[X], each of degree less than p, satisfies

    sum_i c_i(n modp)*W(n+i)=0 for EVERY integer n.

Fix m modulo q. CRT lets n modp range over Fp while n modq=m; thus
sum_i W(m+i)c_i(X) vanishes at every field element. Its degree is below p, so
every coefficient is zero. A nonzero coefficient column of the polynomial
tuple therefore supplies a nonzero constant-coefficient annihilator R of W,
with degree at most r. The minimal annihilator divides X^q-1. This polynomial
is separable because p!=q. Nonconstancy requires a factor other than X-1, and
every such irreducible factor has degree ord_q(p). Therefore r>=ord_q(p).

No r<q hypothesis is needed. This only excludes small global recurrences when
ord_q(p) is large. Ordinary prime-field curves alone do not imply that bound.
An identity on one finite interval cannot use CRT in this way. Degree>=p
coefficients can vanish as functions without being zero polynomials. The lemma
does not exclude local structured evaluators or prove an elliptic-factorial
complexity lower bound. No claim about a specific BGS runtime is proved here.

## Imaginary-quadratic norm lemma

For an imaginary quadratic order with discriminant D<0 and integral basis
1,omega, a noninteger element psi=a+b*omega has b!=0 and

    N(psi)=(a+b*Re(omega))²+b²*|D|/4 >= |D|/4.

The statement concerns that order, not a general quaternionic endomorphism ring.
It does not lower-bound the cost of evaluating a factored isogeny chain. In
particular, a small order of one ideal class does NOT imply a small class group;
a large finite group can contain elements of small order. The proposed class
relation heuristic and concrete1100M/2600M/20000M estimates were not calibrated
or sourced here. No universal interpolation between two chosen regimes follows.

## Other nonaccepted exclusions

The height-bounded factor-base card compares one level's monomial weights.
That does not prove equality of all shifted lattice determinants, useful root
conditions or algorithmic complexity. Additional variables, coprimality and
homogeneity require a full specified lattice argument. S4 also has degree4 in
each variable, so the report's degree2 assertion for the m=3 case is incorrect.
Root checked this in [Semaev2015, section2, PDFpage3](https://arxiv.org/pdf/1504.01175):
S_m has degree2^(m-2) in each variable. The alternative chain of S3 equations
has degree2 per variable but introduces additional intermediate variables; it
is not the card's stated2m-variable direct S4 formulation. The original2004
ePrint PDF fetch returned403; the author2015 arXiv paper was successfully read
at the definition and chain passages. No binary-field complexity claim from
that paper is transferred to the ordinary prime-field challenge.
No advantage was constructed, but the universal determinant exclusion is not
accepted. Factor-base generation, relations and linear algebra remain paid.

Non-group coordinate maps generally break the CURRENT affine label invariant;
this does not prove that no richer invariant or recovery method can work.
Similarly, a norm bound and a selected endomorphism cost do not exhaust all
coordinate-aware mechanisms. Prior-character bounds require their exact degree,
norm, target-character and transport assumptions. No general ordinary-curve
impossibility or current literature saturation is established by this report.

Disposition: no surviving executable operator or credible full-work gain. Retain
the two scoped algebraic lemmas and the open missing-operator conditions. Reopen
on an explicit construction or directly read primary result, not a repetition
of broad unproved negative claims. Main square-root reference unchanged;
verified improvement NONE.

Process: initial Factory Fable task ID in H036-information-fable-raw.md; native
Astra /root/h007_additive_relations independently checked the recurrence and
norm lemmas and their restrictions. Root checked the proofs and rejected the
unsupported generalizations. All read-only; no numerical or solver execution.
