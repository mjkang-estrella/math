# H029 translation-fill model: exact conditional collision/work formulas

2026-10-08. Root and native Astra independently checked elementary finite
probability and accounting. This is a deliberately specified IDEALIZED model,
NOT the collision law of H027's actual deterministic coordinate buckets. No
simulation, new instance, algorithm improvement or Lean theorem is claimed.

## Model and exact expectations

Partition a cyclic order of q positions by m marked endpoints, with positive
gap lengths l_i summing to q. Each new jump output is independent uniform over
all q positions. Translate forward to the next marked endpoint. Its index J has
probability w_i=l_i/q; conditional on J=i, residual fill R is uniform on
0,...,l_i-1. Put kappa=sum_i w_i². Then

    E R = (sum_i l_i²-q)/(2q) = (q*kappa-1)/2.

This is size-biased gap sampling. Replacing it by the unweighted mean gap is
incorrect. With an initially EMPTY visited-endpoint set, let N count jump draws
through and INCLUDING the first repeated endpoint. If e_n denotes the elementary
symmetric polynomial in w_1,...,w_m, then

    Pr(N>n)=n!*e_n(w),
    E N=sum_(n=0)^m n!*e_n(w).

The first equality counts all ordered distinct endpoint sequences. If endpoint
i0 is already visited, subsequent-jump expectation instead is
sum_(n=0)^(m-1) n!*e_n((w_i)_(i!=i0)). Initialization conventions cannot be mixed.

For fixed jump cost Jcost and translation-step cost Fcost, charge the full fill
on the repeated final draw. The empty-visited convention gives exactly

    E W = [Jcost + Fcost*(q*kappa-1)/2] * E N.

Proof: whether draw j is attempted depends only on previous draws, independently
of the current (endpoint,residual) pair. Sum expected attempted-draw costs. This
does not assume N independent of individual costs. Initial setup is separate.

An elementary union bound yields Pr(N<=n)<=n(n-1)*kappa/2. Thus
E N >= sum_(n=0)^K [1-n(n-1)*kappa/2] whenever the summands are nonnegative,
with exact sum K+1-kappa*K(K+1)(K-1)/6. Taking K=floor(1/sqrt(kappa)) also
shows E N>=1/(2sqrt(kappa)), since every retained survival term is at least1/2.
This bound is weak but rigorous for this model alone.

## Conditional sparse-fill illustration

For equal gaps l_i=32, q=32m, E R=31/2 and E N>=sqrt(m)/2. At Fcost=5M and
nonnegative jump cost,

    E W_fill >=155/(16sqrt2) M sqrt(q) >6M sqrt(q).

Astra separately checked root's algebra. The accepted HEURISTIC negation-rho
leading-arithmetic reference with0<=S/M<=1 is at most3sqrt(pi)M sqrt(q)<6M sqrt(q).
Thus this exact equal-gap, fresh-uniform-jump MODEL cannot support the imported
rho headroom even before mixer cost. This is a conditional model falsifier only.
In particular q=32m is not a prime-order instance; almost-equal gaps need a
separate calculation, not substitution. No numeric5.09 or universal delta
barrier follows. Starting with a visited marker changes finite expectations.

Equal gaps generally give the usual finite birthday product on m endpoints.
In a sparse regime m=delta*q, fill work has order Fcost*sqrt(q/delta), under
these hypotheses. Arbitrary gap shapes change both kappa and residual costs;
density alone is not their replacement. Actual coordinate-defined jump outputs
are not proved independent uniform, nor are their gaps known to be equal.

## Detection and applicability obligations

A macro endpoint repeat in a fixed map puts later iterates on its cycle. If
that cycle has no REPORTABLE endpoint, a marker-only reporting scheme never
detects it without a cap/restart. Under an additional independent reporting-mark
model with probability theta, a c-endpoint cycle is entirely unreported with
probability(1-theta)^c. Otherwise delay is the paid traversal to a reported point,
not automatically an independent geometric tail. Interior point reporting is a
different contract and can detect earlier; the present lower work estimate must
not be applied to such a detector without proof.

Actual H027/H029 hypotheses must specify joint jump/gap law, nonzero useful
recovery coefficients, reporting, null trails, starts/restarts and terminal work.
Conceptual scalar-order gaps are analysis objects, not free solver advice or an
admitted enumeration. These model formulas do not authorize a new experiment or
reject every coordinate-aware walk. They sharpen what a candidate must justify
before borrowing a random-map collision constant. Main verified improvement NONE.
