# H008 hyperplane-selector count audit and scoped reconciliation

Primary paper: [Mahalanobis2607.09814v2](https://arxiv.org/html/2607.09814v2),
dated2026-08-06, sections5–6 and Table2. The paper itself does not claim a current
speedup over exhaustive search. Both independent reviewers inspected its actual
algorithm and reported duplicate counting. Raw reports are retained separately;
their strongest probability/cost claims are NOT adopted wholesale.

## Root-checked combinatorial correction

Fix two index halves D,S each of size L, and defect1<=d<=L. The specified full
sweep chooses b subset D of size L-d and completes it with d indices from the
remaining L+d. Its distinct size-L candidate family is

    F = {R subset D union S: |R|=L, |R intersect S|<=d}.
    N = |F| = sum_{k=0}^d binom(L,k)^2.

A fixed candidate with k indices in S contains L-k indices in D. It is visited
once for every b contained in those indices, hence binom(L-k,d-k) times. Thus

    M = binom(L,d) binom(L+d,d)
      = sum_{k=0}^d binom(L,k)^2 binom(L-k,d-k).

Treating these M visits as independent events counts identical predicates more
than once. This is an exact combinatorial defect, stronger than a generic warning
that distinct events might correlate. It does not require a random-matrix model.

The full sweep's prescribed number of penultimate-kernel computations is

    H = binom(L,d) binom(L+d,d-1) = M*d/(L+1) >= N*d/(L+1).

This is a deterministic full-sweep ledger, not an arbitrary adaptive/restart lower
bound. Early success, rank failures, reuse of a fixed pool and value-dependent
choices require separate analysis. A general partial-run bound does not follow
just from this identity. Paid matrix construction/arithmetic only adds to H.

For independent uniform scalar labels over the order-q field, a fixed nonempty
P-side subset and each fixed Q-side R define a nonzero linear equation. Its
probability is1/q; distinct R give nonproportional forms because the P-side
coefficient fixes the proportionality. The count X of hits then satisfies
EX=N/q, EX²=N/q+N(N-1)/q². Union and second-moment bounds give

    (N/q)/(1+N/q-1/q) <= Pr[X>0] <= min(1,N/q).

This is the UNCONDITIONED iid model. Conditioning on distinct points/scalars,
valid fixed pivots or useful coefficients is not exact independence. A justified
bad-event bound can transfer it; that bound and the actual stopping schedule are
under independent native review. Neither reviewer may silently replace the fixed
pool's dependent new guesses by fresh independent draws with cost1/success.

## Exact arithmetic cross-check of two printed rows

Source Table2 supplies floor-log counts but omits L. Root enumerated all integers
d<=L<=4*bits matching BOTH printed binomial floor logs. Monotonicity of these
binomials excludes larger L after their floors exceed the printed values.
The following decimals summarize exact integer/rational calculations, not a
solver experiment or observed success rate. q>=2^bits, so N/2^bits is an upper
bound in the unconditioned model.

| bits | d | matching L | N/2^bits | M/N | reported probability |
| --- | --- | --- | --- | --- | --- |
|100|17|60|0.1384313342|108.2426383|0.98464|
|100|17|61|0.2641456525|100.5613820|0.98464|
|104|18|59|0.0251507271|207.5558517|0.94277|
|104|18|60|0.0508402247|190.6880063|0.94277|

This resolves the raw reviewers' inconsistent reconstructed L values: neither
printed row uniquely identifies L. Small excluded-event conditioning cannot
bridge these gaps if its claimed negligible bound is proved. No exact numerical
success probability or unknown author parameter is inferred from these decimals.

Reproduce the integer-count check (Python3 standard library, no random seed):

```python
from math import comb
from fractions import Fraction
for bits,d,fh,fo in [(100,17,53,48),(104,18,55,49)]:
    for L in range(d,4*bits+1):
        C,K=comb(L,d),comb(L+d,d-1)
        if (C.bit_length()-1,K.bit_length()-1)!=(fo,fh):
            continue
        N=sum(comb(L,k)**2 for k in range(d+1))
        M=C*comb(L+d,d)
        H=C*K
        assert M==sum(comb(L,k)**2*comb(L-k,d-k) for k in range(d+1))
        assert H*(L+1)==M*d and H*(L+1)>=N*d
        print(bits,d,L,Fraction(N,2**bits),Fraction(M,N),H)
```

The actual inline command additionally printed the provisional expression
(N+5L²+2)/2^bits supplied by the raw review. Its coefficient for bad events has
not been established and is NOT used as an accepted probability bound. Exact
count identities passed; no curve instances, timings or asymptotic fits were run.

## Independent review and accepted scope

Native Astra /root/h007_lattice_carries completed independent source/math review.
It confirmed U=N, M and H identities. The anti-diagonal helper is insufficiently
specified to certify every pivot-handling assertion made in the raw reports.
Let alpha be the admissibility probability in the ideal model conditioned only
on nonzero P-side target t. Q-side iid labels still give the same per-event and
pairwise probabilities under that single conditioning. After full admissibility,
the safe upper bound is s<=min(1,N/(q*alpha)); exact independence is not claimed.

For independently regenerated admissible inputs with fixed index choices and
the entire H-computation sweep charged each time, expected computations per
success obey H/s >= q*alpha*H/N >= q*alpha*d/(L+1). For alpha bounded below and
L=O(log q), this specified strategy costs Omega(q/log q), before matrix setup,
field arithmetic and memory. A single completed sweep with constant success
likewise needs that scale of work. It is not a square-root improvement.

The paper also describes early stopping. Under a fixed enumeration order and
union-size-exactly-d rule, h inserted penultimate subsets can complete at most
(L+1)h/2 candidate sets: each inserted subset has only L+1 one-row extensions,
and every completed candidate needs two inserted subsets. This is a fixed-prefix
combinatorial bound, not automatically an adaptive/restart cost theorem. False
alarms, rejected larger unions, rank-failure channels and index choices need
explicit handling in a complete early-stop algorithm analysis.

The raw unrestricted claim that ANY restart policy needs Omega(q/L) insertions
is withdrawn. Setup screening can solve an instance with zero insertions; retained
cross-batch point-collision hashes can implement known birthday attacks before
constructing a dense matrix. Reusing a matrix also does not create fresh independent
trials. In particular q/L+L²=>q^(2/3) must not be stated
for every large-pool algorithm while ignoring cheap upstream point collisions.
Factory's blanket exact independence after pivot conditioning is not accepted.

The duplicate-count objection stands independently of these withdrawn claims.
The finite table mismatch is conditional on fixed indexing and a high-probability
admissibility event. We do not adopt a precise all-screening correction without
the missing helper details. No broad coordinate-aware lower bound follows.

No matrix experiment authorized. The proposed comparison would primarily test
an already specified group-sum equivalence; an excess is first an implementation
or model disagreement, not automatically a new attack. A million kernel solves
is not a million total instrumented events. Its claimed60s cap fit is unvalidated.
Availability statement is only that reviewers found no linked/public code in
their search, not proof that no implementation exists anywhere.

Best supported classical full-range reference remains square root. Verified
improvement NONE. The new selection mechanism has not survived full-cost review.
An explicit value-dependent selector with justified useful-collision behavior
could change the conclusion; merely naming a rho walk on kernel lines cannot.
