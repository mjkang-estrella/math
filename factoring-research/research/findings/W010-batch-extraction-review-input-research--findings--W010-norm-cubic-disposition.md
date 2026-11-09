# W010 cubic sampler — parent disposition

2026-10-08. A terminal result read. All 12 delivery artifact hashes verified;
22 exact symbolic certificate checks are recorded. No candidate runs or new
factoring complexity bound. The original hypothesis remains as a historical
proposal; the corrections here govern its subsequent use.

Accept equations (1)–(6) and the self-contained conic count in the
[review](W010-norm-cubic-review.md). Uniform-start values after the update
are expectations conditional on legal acquisition, not pointwise values.
The displayed third cubic root can coincide with a sampled root and cannot
be counted as a third distinct occupied fiber automatically.

The review resolves an actual bottleneck: the sign of the expected residual
drift is positive for EVERY symmetric law with a legal pair. Its proof is
accepted. Write S=v^2-2q4. The four-element sign/interchange orbits give

    sum K(beta)^2 = 4S+R,   R>=0.

At beta=a^2, the vertices +-a are excluded from the legal quadratic relation.
Every remaining vertex has degree at most two, so

    K(beta)<=2(v-A(beta)),
    sum K(beta)A(beta)<=2v^2-4q4=2S.

Therefore the raw acquired drift satisfies D_v>=2S+R, strictly positive
when ell>0. This proof applies to reachable laws as well as arbitrary
symmetric laws. Withdraw the original suggestion that weighted root removal
could defeat the raw expected drift. Individual updates can still lose
residual mass, as the review's fixed symbolic example shows; it carries
no reachability assertion.

The bound alone gives no favorable concentration time. Initially S is of
order p^-2 and R of order p^-1. Showing that R is large compared with S
therefore does not demonstrate accelerated concentration. Nearly one-pair
support can make S and the legal probability small. Favorable acquisition,
CRT separation and evaluator work still need quantitative control.

Accept statewise CRT factorization for distinct primes p,q>3, with stopped
states frozen. The expected residual process is a submartingale under that
protocol; this is not a claim about conditioning on continued failure.
For T raw attempts at depths j_t, sequential acquisition costs
O(sum(j_t+1)), at most O(T(k+1)). O(k^2) covers k raw attempts or a
no-failure k-update construction, not an unlimited wait for k accepted
updates. A final P(P-a) absorption phase is no longer odd and must not
inherit the training laws without justification.

The literal signed-reservoir capacity sharpens to floor(M/2)-1 accepted
mergers for M initially distinct signed values. This closes only that stored,
globally updated pool. It does not rule out lazy/compressed acquisition.

Next constructive question: determine the RATE of weighted norm energy
growth along the paid process. The parent is deriving a smooth-leading-form
Fourier envelope for short cubic circuits, while retaining the separate
scalar-computation route. The Jacobi-filter extension changes the sampler;
the positive-drift theorem is not automatically inherited by that extension.
