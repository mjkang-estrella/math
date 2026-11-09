# W003 parent gate — a totally positive, norm-certified quadratic generator

2026-10-08. **Provisional symbolic deductions; UNACCEPTED pending independent
review.** Verified new complete classical factoring improvement: **NONE**.
This note changes the field law; it supplies no mixed-target algorithm or
useful-target probability. No experiment, implementation or Lean action follows.

## Question and prior-art boundary

The [accepted Lens A disposition](W003-twisted-disposition.md) excludes the
positive-binomial selector because its generator has a negative real conjugate.
The question here is whether one can explicitly remove that obstruction while
retaining a simple modular root and charging construction. This is narrower
than finding the required product of rational-pair rows in two fields.

Solving a bivariate modular norm equation is established prior art. It must
not be confused with extracting a prescribed modular square root. The source
check found the following, with different verification levels:

- Shallit, *An Exposition of Pollard's Algorithm for Quadratic Congruences*,
  author-hosted [primary report](https://cs.uwaterloo.ca/~shallit/Papers/pols.pdf).
  Read sections I–IV and VI–VIII; section V was read as a source example,
  not executed. Pages 7 and 9 were visually checked. The norm-composition
  and coefficient-reduction procedures are explicit. The displayed fast
  running-time estimate in section IV depends on a conjectural least-prime
  bound in an arithmetic progression. Page 7 explicitly distinguishes a
  naive sum-of-two-squares prime search from a different referenced method.
  This archive does not verify an unconditional polynomial-time routine.
- Pollard–Schnorr (1987), DOI
  [10.1109/TIT.1987.1057350](https://doi.org/10.1109/TIT.1987.1057350):
  metadata/abstract only in this gate; the full article was not obtained.
- Adleman–Estes–McCurley (1987), *Solving Bivariate Quadratic Congruences in
  Random Polynomial Time*, Math. Comp. 48(177), 17–28,
  [DOI](https://doi.org/10.1090/S0025-5718-1987-0866095-8). Its abstract
  reports removal of unproved hypotheses. The full theorem, domain and
  algorithm were **not retrieved or verified** here. AMS returned 403;
  JSTOR's web view supplied no article; the USC author bibliography listed
  the paper without a download link; a located journal mirror was unreachable.
  No unconditional all-input complexity claim is imported from the abstract.
- Boneh–Gentry–Hamburg, *Space-Efficient Identity Based Encryption Without
  Pairings*, [author PDF](https://theory.stanford.edu/~dabo/papers/bgh.pdf).
  Read section 5 through Lemma 5.2, Appendix C and the beginning of C.1;
  visually checked page 9. Their construction lifts a modular conic to
  integer ternary forms. Lemma 5.2 leaves running time dominated by producing
  two suitable primes; section 5.2 explicitly attributes a GRH qualification
  to Pollard–Schnorr. This is useful primary algorithm evidence, not an
  unconditional uniform bound for scanning short progressions. The paper's
  unit-denominator and coefficient hypotheses must be checked before reuse.

The 2018 ECCC report 149, section 8.1.2, led to BGH but was not used to
strengthen its theorem. These are bounded source checks, not a novelty proof.
Full source identities and failed direct retrievals are preserved under
[W003-normgate-evidence](W003-normgate-evidence/access.json).

## Explicit modular subproblem, including a finite paid reference

After elementary cases, assume N is odd, gcd(N,15)=1, and R is a unit
represented by 1<=R<N. A proper gcd with 3 or 5 is an earlier verified factor;
their prime/power cases belong to preprocessing. No hidden root x is passed.
Define Norm2(N,5R) to return integers 0<=u_0,v_0<N with

    u_0^2+v_0^2 = 5R (mod N),

or a verified proper factor. Every returned pair is checked. Its actual time,
space, randomness, failure and restart behavior must be charged.

There is at least one such pair. For each odd prime p dividing N, the sets
of squares and 5R minus squares in F_p each have (p+1)/2 elements, so they
intersect. Since 5R is a unit, at least one coordinate of a solution is
nonzero. Its corresponding derivative is nonzero, so it lifts successively
to each p^e. CRT proves existence modulo N. This proof uses the factors
only for analysis, not as inputs to a proposed solver.

A finite deterministic reference constructs the N records (a^2 mod N,a),
sorts them, and constructs/sorts the N complementary records
((5R-b^2) mod N,b). A merge finds a common first coordinate. A sequential
merge sort uses O(N poly(log N)) bit time and O(N poly(log N)) space, including
full construction, comparisons and reads. Thus this note can instantiate
Norm2 without an oracle, at a power-scale cost. This is a paper algorithm,
not an implemented solver or a claimed improvement. A cheaper replacement
requires its own fully checked source theorem or algorithm proof.

## Conditional transform of any verified Norm2 output

Given the pair, set

    u=u_0+4N, v=v_0, s=u^2+v^2, t=2R,
    f(T)=T^2-sT+t^2, Delta=s^2-4t^2.

Then 16N^2<=s<26N^2. All integers in this construction have O(log N) bits,
and its overhead after Norm2 is polynomial. Since 16R^2<2s-1,

    (s-1)^2 < Delta=s^2-16R^2 < s^2.

Delta is a positive nonsquare integer. Thus f is irreducible over Q, its
degree is two, and both real roots are positive: their sum is s>0 and
product is t^2>0. Let K=Q(alpha), f(alpha)=0. No discriminant factorization,
maximal order or class-group computation is needed for this construction.

The modular identities are

    s=5R (mod N), f(R)=0 (mod N), f'(R)=-3R (mod N).

In particular the derivative and s are units. The simpler discarded choice
t=R, s=2R mod N would instead force f'(R)=0 mod N; it cannot be substituted
into a derivative-cleared recovery argument. The t=2R choice fixes that
specific error. This note does not construct two distinct fields.

## Square-root branch and explicit norm certificate

Before using a quadratic extension of K, test the positive integers
s-4R and s+4R for exact integer squares. If k^2=s-4R, return y=k mod N;
if k^2=s+4R, return y=k/3 mod N. The inverse of 3 exists, and both answers
satisfy y^2=R. Verify them. This is an N,R-only root return, not a claim
that such a square occurs frequently under any particular Norm2 sampler.

These tests also decide whether alpha is a square in K. If w^2=alpha,
w is integral and Norm(w)=+t or -t. Hence

    Tr(w)^2 = Tr(alpha)+2Norm(w) = s+2t or s-2t.

The trace is an integer. Conversely, if k^2=s+2t, then
((alpha+t)/k)^2=alpha; for k^2=s-2t use (alpha-t)/k. The denominators are
nonzero because s>2t. Therefore on the continuing branch alpha is nonsquare
and L=K(beta), beta^2=alpha, really is quadratic over K.

Define elements of K

    A=(u alpha+v t)/s, B=(v alpha-u t)/s.

Using alpha^2+t^2=s alpha and u^2+v^2=s gives

    A^2+B^2=alpha.

B is nonzero: if v!=0, B=0 would make alpha rational; if v=0,
B=-ut/s!=0. Consequently

    Norm_(L/K)((A+beta)/B) = -1,
    Norm_(L/K)(beta*(A+beta)/B) = alpha.

Thus this changed generator avoids both the negative-real-conjugate
obstruction and the necessary obstruction that alpha not belong to the
relative norm group. This is only an explicit field identity. It does not
show alpha is a square, nor a product of the allowed rational-pair rows
times a square. In particular A and B depend on alpha; they are not both
rational coefficients of a row a^2-b^2 alpha.

## Reduction and what remains missing

The sum-of-two-squares identity reduces through the localization at s:

    Abar=(u+2v)/5, Bbar=(v-2u)/5,
    Abar^2+Bbar^2=R (mod N).

These are just a rational rotation/scaling of the supplied modular norm
representation. They are not a modular square root. A proper gcd of Bbar
with N would give a factor; Bbar=0 mod N would make Abar a root. Those
events can be checked and priced, but no frequency is established here.
The field expression with 1/B cannot automatically be reduced: its image
needs an additional unit test. No map from the entire number field to
Z/NZ is being assumed.

Even with a fast Norm2 routine, this note has not supplied:

1. Two distinct fields at a useful height/degree cost under one specified law.
2. A list of common rational pairs whose square classes attain a mixed target,
   or an algorithm that finds it with a proved completion probability.
3. Cheap norms and a relation-supply theorem for those actual pairs.
4. Complete factoring cost inclusive of all failures, extraction and restarts.

The original W003 integer twist and field norm/involution deductions are under
a separate Lens B review. They do not confer useful mass on this selector.
Nor may polynomial interpolation between two field targets silently invert
a resultant divisible by N because the fields share R modulo N.

## Disposition and next decisive work

**Provisional revision, not a speedup.** The complete finite reference costs
O(N poly(log N)) merely to obtain the norm representation; the transform then
costs poly(log N). An independently verified faster modular norm theorem
could improve this input-construction stage, but would still leave the actual
mixed-target construction missing. No complete factoring bound is derived.

Request an independent review of these elementary identities, square test,
localization, exact prior-art scope and paid reference. The source reviewer
should make a bounded attempt to obtain AEM's full primary theorem, explicitly
preserving a retrieval limitation if unsuccessful. The useful next mathematical
question is whether this changed field law enables a finite rational-row
target construction, or has a further separating character. Do not spend a
numerical wave testing the already impossible positive-binomial selector.
