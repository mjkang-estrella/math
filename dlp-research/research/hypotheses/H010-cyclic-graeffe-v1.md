# H010 cyclic Graeffe selector v1: frozen operation, reviewed rejection

Native Astra /root/h006_structured_relation_ideas proposed this independently.
The original CYCLIC specification is retained below. Independent paper review
now rejects its literal sparse schedule: see
[the first-block obstruction](../findings/H010-cyclic-graeffe-obstruction.md).
No implementation or improvement is accepted. Standard Graeffe/root recovery is prior art; no novelty claim.

## Public family and setup

Require p>3, ordinary short-Weierstrass E/F_p of full prime order q~p,
G,Q in E(F_p), and
B_i=ell_i^k_i~B=q^(1/5), ell=(2,3,5,7,11), k_i>=1, N=product B_i | p-1, N~q.
The disjoint fixed-prime supports make the five domains coprime. A growing
representative prime family with paid efficient generation is UNPROVED, not
implied by choosing these integer sizes. No arbitrary-prime/secp256k1 transfer.
Charge candidate parameters, order/primality checks, subgroup generation and all
failures. For supplied parameters, remove the five primes from p-1 and verify
the sizes/cofactor. Sample c in F_p^*, set gamma=c^((p-1)/N), and verify
gamma^(N/ell_i)!=1 for the five primes, charging all rejected candidates.
Nonzero sampling and this exponentiation guarantee gamma^N=1.

Fix public shifts u_i before targets. Enumerate V_i=u_i+mu_(B_i), valid curve
points/signs, nonresidues and duplicates; the O(B) actual factor-base logarithms
are unknown. Each query samples labelled R=aG+bQ, with infinity handled and
charged separately. Construct the actual S6 specialization

    f_R(T)=S6(u1+T^(N/B1),...,u5+T^(N/B5),x(R)).

Full coefficient construction and reduction modulo T^N-1 are paid. No precomputed
inverse table or free S6 oracle. Large fixed-arity constants remain material.

## Frozen transform schedule

Process all k1 factors2, then all k2 factors3, then5,7,11. Denote successive
factors d_j. Set a0=1,n0=N,a_(j+1)=a_j*d_j,n_(j+1)=n_j/d_j. Store g_j as an
ordered sparse map of nonzero coefficients with canonical exponents0<=e<n_j.
Start g0=f_R mod(T^N-1).

Set zeta_j=gamma^(N/d_j). Form, in increasing t and multiplying left to right,

    h_j(X)=product_{t=0}^{d_j-1} g_j(zeta_j^t X) mod(X^n_j-1).

Every sparse multiplication explicitly visits all input term pairs, adds/reduces
exponents modulo n_j, multiplies coefficients, updates the ordered dictionary
and deletes zero entries. Charge all phase-table creation, exponent arithmetic,
comparisons, allocations and transient entries later cancelled. No fast Fourier,
compressed determinant, dense multiply or support oracle is substituted silently.

Only exponents divisible by d_j survive in canonical h_j. Divide these exponents
by d_j to obtain and store g_(j+1), with degree<n_(j+1). This follows because
X->zeta_j X is an automorphism of the quotient ring and permutes the product
factors; p does not divide d_j. The exact predicate to verify independently is

    g_(j+1)(y)=product_{x in mu_(n_j), x^d_j=y} g_j(x).

The children are distinct; over the field a product is zero exactly when one
child is zero. No modular counting, simple-root assumption or free squarefree
reduction is used. At n_s=1, nonzero g_s certifies no raw-grid root.

## Stored-layer witness descent

A level-j node is a KNOWN integer k, 0<=k<n_j, representing gamma^(a_j*k).
Start at level s,k=0. A level-(j+1) node k has level-j children
k+t*n_(j+1), 0<=t<d_j. Compute field values and evaluate stored g_j; visit zero
children depth-first in increasing t. No unknown subgroup exponent is recovered.
Store or recompute only with the actual cost charged. Distinct parents have
disjoint children. Zero intermediate polynomials cause more paid branches.

At each root leaf reconstruct all five coordinates, test curve membership and
signs, and verify the actual point relation. Continue past unusable roots. Return
at most ONE verified relation per query. Full exhaustion means no usable relation;
cap exhaustion is inconclusive and a paid failure. Actual sparse linear algebra
must eventually give a dependency with nonzero Q coefficient; charge dependent
rows, failed matrices/restarts and final scalar verification. No free rank oracle.

## Full-work gate

Let K include complete query construction, every cyclic convolution/update,
stored-layer evaluation, descent, bad roots and verification. Useful query yield
sigma and relation-rank assumptions are unproved. The conditional collector
ledger is setup+~O(B*K/sigma+B²), requiring K/sigma=o(B^(3/2)); an exponent gain
requires a fixed power margin. The squared-support bound for elementary
convolutions and charged exponentiation/evaluation gives at best a sufficient
~O(S²+V*S) TRANSFORM/DESCENT bound when S bounds ALL input, output and temporary
supports and V counts node evaluations. Query construction is an additional
explicit term unless separately bounded by that expression. Do not silently
omit it. Memory includes O(S log q) stored-layer records, temporary maps,
traversal, factor-base data and relation systems.

With S=B^rho, V=B^nu, sigma=B^-s, a sufficient transform/descent condition is
max(2rho,rho+nu)+s<3/2, plus paid setup/construction/linear-algebra bounds.
No such bound is known. Small final scalar, few roots or shrinking modulus do
not establish small intermediates. H009's quotient proof does not apply directly.

Primary prior art cited by proposer:
[Grenet–van der Hoeven–Lecerf](https://www.texmacs.org/joris/dmodroots/dmodroots-abs.html),
[Grenet–van der Hoeven–Lecerf tangent Graeffe](https://www.texmacs.org/joris/rmodroots/rmodroots.html).
Independent review must check both the invariant and actual cyclic work at a
specified stage, e.g. after eliminating the2-power block. Degree alone is not a
sparse cost lower bound. No numerical pilot or new engine yet justified.

## Separate split-fiber proposal: conditional coefficient cancellation

The proposer also considered functions f_i with pole divisors D_i and labelled
pole sums C_i=a_iG+b_iQ, sharing a polynomial composite h=H_i(f_i). For d_i=deg f_i,
D=deg h<q and n_i=D/d_i, the literal pole identity is Pole(h)=n_i D_i. If matching
these divisors has not already produced a useful collision between distinct
labels of the same point, labels satisfy b_i=(d_i/D)b_h modulo q. A dependency
among COMPLETE fiber rows has sum c_r*d_i(r)=0 after its point columns cancel,
so its Q coefficient also vanishes. Ramification multiplicities preserve this.

This is a conditional rejection of the supplied complete-fiber dependency stage,
not a lower bound on every common-composite algorithm or a dismissal of a useful
collision discovered during pole matching. No cheap way to construct such a
collision was supplied. Rational outer maps or other divisor arrangements need
new operations and cost analysis. No rank experiment or function-field engine.

## Review clarifications

Native independent review confirms the norm/descent invariant on paper. Gamma
generation samples F_p^*, not the full field: zero would pass inequalities
gamma^(N/ell_i)!=1, so its exclusion or gamma^N=1 is mandatory.
For split-fiber cancellation the dependency must cancel COMPLETE zero-divisor
columns with multiplicities, including known-log points and O, or retain their
degree contributions explicitly. Dropping such columns before dependency search
does not justify sum c_r*d_i=0; that altered algorithm is outside the rejection.

Root checked the linked primary abstracts/introduction. The randomized paper
starts with a separable monic polynomial that splits over the field and excludes
certain precomputed primitive-element/factorization costs. These assumptions and
its root-finding improvements do not establish the required complete CRT relation
query bound here. Completed prior-art review and root qualifications are retained in
H010-graeffe-priorart-disposition.md under findings.

## Reviewed cost disposition

Native Sol derived and native Astra/root independently checked a first-2-block
coefficient-face argument. At a=2^t comparable to min B_i/32, entire-box CRT
injectivity preserves at least16a+1 terms outside x(R)=u2. The NEXT frozen
convolution visits Omega(B²) pairs. A cap-independent work/reward argument
rejects the proposed Theta(B)-row uniform collector at Omega(B³) expected cost.
This is a paper result, not Lean formalization or an all-algorithms lower bound.
The earlier open cost questions above preserve the proposal as it was reviewed;
the linked finding supplies the current disposition. No numerical pilot needed.

The square-root reference is an available classical algorithm, not a claim of
optimality on every supplied curve. Ordinary does not exclude anomalous q=p
curves; those and other known easier special families must be excluded before
claiming that reference is the strongest applicable baseline. The literal-work
obstruction itself does not need that hardness exclusion. For R=O and b!=0,
aG+bQ=O directly gives the scalar; charge this rare exceptional event, while
b=0 produces no useful row. The finding explicitly accounts for infinity.
