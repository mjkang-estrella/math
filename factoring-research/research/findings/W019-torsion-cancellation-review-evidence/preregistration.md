# W019-B certificate preregistration (single run)

Written before `certificate.py` was executed. Code hash is recorded in
`preregistered-manifest.json` after this file and the code are frozen.
The certificate gets one run under this preregistration, with no tuning or rerun.
Every assertion outcome, failure, or abort is kept in `certificate-output.json`
and `certificate-stderr.txt`.

## Purpose and non-purpose

This is a finite abstract-group and quadratic-form consistency check of the
review's hand proofs. It is NOT a performance measurement, NOT a statement about
the distribution of class groups, and NOT a factoring experiment. It does not use
the factoring_lab solver harness.

## Budgets

- Wall clock: 60 s hard timeout (`timeout 60`).
- Event budget: 20000 events. One event = one algorithm group operation in part I
  (doubling, addition or subtraction in an abstract group) or one form composition
  in part II. If the counter would exceed 20000, the script aborts and records it as
  a failure. Brute-force *verifier* work (enumerating <A,B>, listing reduced forms,
  reduction steps) is not metered as events; it is bounded by the wall clock.
- No randomness; enumeration is exhaustive over the fixed inputs below.

## Part I: abstract abelian 2-groups (additive Z/2^e1 x ... x Z/2^er)

Groups: cyclic [2], [8]; noncyclic [2,2], [2,4], [4,4], [2,8], [2,2,2].
Every pair (A,B) with A != 0 is run. J := top involution of A, which is known to the
algorithm. Algorithm `cancel(A,B)` is W019 (B1) plus the swap rule: if ord B > ord A
and top(B) = J, swap the roles. The output is either a useful involution
(in G[2] \ {0,J}) or FAIL.

Assertions:
- I1 termination/correctness: every output is FAIL or an element Z with 2Z=0,
  Z not in {0,J}, Z in <A,B>.
- I2 criterion: output != FAIL  <=>  <A,B> is noncyclic (brute force check).
- I3 cost: group operations per run <= m(m+5)/2, where 2^m = max(ord A, ord B).
- I4 maximal-order pivot: for every noncyclic G and every A of maximal order
  (= exponent of G), #successful B / |G| = 1 - 1/[G:<A>] >= 1/2.
- I5 counterexample family: G = C2 x C_{2^k}, k=1..5, A = J = (0,2^(k-1)):
  the success count over all B is exactly 2 (fraction 2^-k). Naive top-involution
  chain success is also exactly 2 of 2^(k+1).
- I6 two-sample pivot upgrade: for every G (noncyclic) and every A != 0,
  P(success within two fresh uniform samples B1,B2) >= 1/4, where after a failed
  run the pivot becomes the larger-order element of {A,B1} (A on ties).

Reported (not asserted): for each noncyclic G and each involution J, the
probability of success of one uniform B when A is uniform among elements with
top(A)=J (the "pivot from a previous unhelpful chain" model), vs the naive
chain probability P(B != 0 and top(B) != J).

## Part II: quadratic forms for odd squarefree semiprimes N = p*q, 15 <= N < 400

D = -4N if N = 1 mod 4, D = -N if N = 3 mod 4. All reduced primitive forms are
enumerated. Each reduced form is squared with Arndt/Dirichlet composition followed by
reduction. Ambiguous := reduced form whose square reduces to the principal form.

Assertions:
- II1 composition self-check: every composed (A3,B3) satisfies 4A3 | B3^2 - D.
- II2 count: #ambiguous = 4 when N = 1 mod 4 and 2 when N = 3 mod 4.
- II3 exact set: the ambiguous set equals the closed-form prediction:
  N=1 mod 4: {(1,0,N), (p,0,q), (2,2,(N+1)/2), X} with X=(2p,2p,(p+q)/2) if q>3p,
  else ((p+q)/2, q-p, (p+q)/2).
  N=3 mod 4: {(1,1,(N+1)/4), Y} with Y=(p,p,(p+q)/4) if q>3p,
  else ((p+q)/4, (q-p)/2, (p+q)/4).
- II4 shape: every ambiguous reduced form has b=0, b=a, or a=c.
- II5 extraction: d(f) = a if b=0; a/2 (D even) or a (D odd) if b=a;
  a-b/2 (D even) or 2a-b (D odd) if a=c. Then d=1 exactly for the principal form
  and (case 1 only) J=(2,2,(N+1)/2); every other ambiguous form gives d in {p,q}.

A failed assertion is reported as a failure of the corresponding hand proof or
of the code. It is not silently repaired.
