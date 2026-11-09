# W008 — four-list audit disposition

2026-10-08. Parent intake of completed task A. The supplied control has
expected sqrt(p)*poly(log N) work for N=pq, distinct odd primes. Verified
improvement over established factoring bounds: **NONE**.

[Review](W008-fourlist-review.md), [frozen evidence](W008-fourlist-review-evidence/),
and [original proposal](../hypotheses/W008.md) are retained. Parent verified
all 23 delivery hashes. The delivery includes all ten frozen input snapshots;
later changes to live STATE/tasks do not invalidate their earlier snapshots.

Accepted: the exact pairwise law and moments for arbitrary independent
uniform lists, union-bound global-zero loss, and one-path full-gcd descent.
Balanced list splitting takes O(log K) calls and cannot reach a full-gcd
singleton on the event that no tuple vanishes modulo N. Multiplicities are
preserved; no assumption of joint independence is made.

The N-only doubling/cap schedule succeeds with probability >3/8 at every
stage from the first K^4>=p to the cap after primes <=127 are removed.
Four independent trials per stage make the quadratic expected-cost tail
summable. This is an expected-time statement, not a worst-case random-tape
bound or an all-composites theorem.

The review repairs the proposed field-resultant shortcut. It checks integer
denominators, constructs one composed sum by fast series on its legal unit
chart, and finishes by monic multipoint evaluation at the other explicit
pair list. A fully explicit monic fallback computes the exact scalar even
when the factorial gcd is nonunit. No generic field-resultant implementation
with unchecked pivots is accepted. Full bit work remains K^2*poly(log N+log K).

Two accounting corrections are authoritative:

- With an exact scalar evaluator costing K^alpha on every required sublist,
  paid random inputs make the trial exponent beta=max(1,alpha), hence
  expected p^(beta/4)*poly(log N). A random-input-only guarantee needs a
  separate theorem for adaptively selected recovery sublists.
- For success through either prime, independent-label filtering uses
  rho=1/p+1/q-2/N, rather than the p-only probability a=(1/p)(1-1/q).
  The corrected fixed-trial materialize-first restart bound is 2/sqrt(rho)
  expected records. It remains Omega(sqrt(p)) and closes only that model.

The exact-scalar reduction to integer four-list equality retains its prime
modulus, arbitrary-input, input-reading and prime-acquisition qualifications.
It is not a general hardness result for factoring or for a random-grid promise.

The mixed-coefficient separation-rank calculation is accepted as a symbolic
obstruction to o(K) separated terms for one quotient element. The parent has
now developed its different Hankel-displacement suggestion into an explicit
[two-factor multiplication test](W008-displacement-product.md), independently
delegated as task C. That new proof remains provisional. No factoring
experiment or source/Lean change accompanies this disposition.
