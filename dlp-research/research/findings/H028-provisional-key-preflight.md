# H028 provisional signed Miller-coefficient key: root preflight

2026-10-08. UNREVIEWED candidate-specific derivation pending separate review.
No numerical experiment, Lean theorem, novelty or complete-work gain claimed.
Source of h identities: accepted H027-compact-trace-construction.md; the key
application itself is a new hypothesis in this project, not a prior-art claim.

## Exact signed bucket normalization

Let E(Fp) have prime order q>2, q!=p. Set h(P)=a_P/q and h(O)=0.
Use c(P)=min(rep(h(P)),rep(-h(P))), including zero as an ordinary bucket.
Let b_t=number of group points in bucket t, B2=sum_t b_t^2, and b0=b_(c(O)).
The value h=0 does not identify infinity; identity dispatch uses the actual point.

If U is uniform on E\{O} and V independently uniform on E, then

    Pr[c(U)=c(V)] = (B2-b0)/(q*(q-1)).

Proof: the all-U sum of bucket sizes is B2. Removing U=O removes b0.
For each nonzero U, precisely V=U and V=-U are genuine signed point matches.
They are distinct since q>2, and both are raw-key matches. Consequently

    Pr[raw match but V not in {U,-U}]
      = (B2-b0-2*(q-1))/(q*(q-1)).

This nonnegative numerator counts ordered false pairs exactly. It avoids the
double counting of h=0 that occurs when adding h(V)=h(U) and h(V)=-h(U).

Choose paid independent uniform s in Fq* and r in Fq, set G'=sG,Q'=Q+rG.
For any fixed nonzero index i modq, U=iG' is uniform nonzero. For any fixed
giant index j and stride D, V=Q'-jD G' is uniform on E conditional on s.
Thus the same pair law holds for EVERY original fixed target Q. For I nonzero
baby indices and J giant indices with fixed full caps, the expected number
of false record comparisons is exactly IJ times the expression above, even
though comparisons are dependent. Nonzero baby indices must not wrap to0.
A decoded k' for Q'=k'G' gives original k=s*k'-r modq.

A production table must retain ALL records per canonical bucket and scan them;
otherwise a spurious representative can hide a genuine collision. Each pair
should be scanned at most once (e.g. insertion queries the opposite table).
The stopped scan count is bounded by the full-cap count. This is only an upper
bound for stopped work, not an exact average stopping-time formula. Identity
and zero-index cases require direct handling and their own paid work.

## What this lemma does not establish

B2=O(q) would imply O(1) expected false scans for I,J=O(sqrt(q)), but that
hypothesis has not been proved or measured for this h. Even with it, archive
traffic, scalar setup, additions, bucket overhead, reconstructed coordinates,
full verification, and finite batch sizes can erase the saved squarings.
The coefficient can be propagated cheaply only while the required full center
and offset data remain available; a discarded point is not a free later input.

The proposed arithmetic block saving is 2*k*ell squarings relative to the
matched H019 x-key schedule. Setup plus false-refinement costs must fit inside
that margin; no time or throughput measurement follows from the arithmetic.
Full deterministic signed-prefix caps already give coverage, so truncation
and rerandomized retries are unnecessary unless a new contract explicitly
introduces them. Use the same caps/overshoot and randomization on the comparator.

A justified next diagnostic would measure the exact signed B2 and b0 across
increasing synthetic sizes and seeds and independently check propagated h
against direct normalized Miller chains, including vertical/identity dispatch.
Its enumeration is paid diagnostic computation, never free production advice.
A finite moment result cannot prove asymptotic control or complete-solver gain.
Exact curves, size/seed grid, budgets and rejection thresholds await proposer
delivery and independent review; no run authorized by this draft.

## Independent review

Factory Opus5.5 NEW task RUNNING:
node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h028-provisional-key-cost-review-factory-opus-20261008-r1

Initial brief supplied h laws, exact claimed block costs, paid archives,
independent s/r randomization, and requested exact signed-fibre probability,
correctness/cost audit plus diagnostic recommendation. This root derivation
was made after delegation; it is not represented as reviewer-approved.
Native proposer has received the derivation for a separate check.
