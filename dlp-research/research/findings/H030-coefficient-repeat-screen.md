# H030 C2 false-repeat screen: exact global count, no visited-rate claim

2026-10-08. Root derived from accepted H028 moment bound; native Astra independently
checked quotient/zero conventions. Candidate-specific paper lemma only, no Lean
claim or numerical test. It supplies a conditional cost input, not a gain.

Exclude O and let N=q-1, m=N/2>1. On nonidentity points write c(a)=|{P:h(P)=a}|,
c0=c(0), M2=sum_a c(a)^2. Accepted H028 bounds give M2<=3N and the fullpoint
canonical signed-h bucket moment S2=2M2-c0². Oddness makes every bucket a union
of two-point negation classes, INCLUDING the zero bucket. If b_t counts classes
per canonical h key, then

    sum b_t=m,
    sum b_t²=S2/4<=3m-c0²/4.

The exact number of ordered distinct-class false screening matches is

    F=sum_t b_t(b_t-1)=S2/4-m<=2m-c0²/4.

For a UNIFORMLY sampled ordered distinct class pair this yields

    Pr(false h match)=F/(m(m-1))
                    <=min(1,(2m-c0²/4)/(m(m-1))).

Each bucket also satisfies b_t<=sqrt(3m). These identities do not say that a
deterministic walk visits independent/uniform pairs, even with a uniform start.
Visited correlations/repetitions can concentrate screening work. C2 must still
pay exact x reconstruction and comparisons on false h repeats, retain adequate
history, and separately dispatch O rather than folding it into this zero bucket.
Use an actual trajectory law or measured complete count before converting the
global bound to a solver overhead estimate. No trial admitted by this lemma.
