# H033 paid narrowing, restarts and portfolios

Status: three native Sol initial policies, independently reviewed by native
Astra and checked by root. Scoped conditional negatives, no verified improvement.
No numerical experiment, implementation or new Lean claim. Proposer:
`/root/h010_early_dependencies`; reviewer: `/root/h007_additive_relations`.

## Paid exclusion followed by an interval backend

For uniform k mod prime q, build signed babies 0,±G,...,±bG, D=2b+1<q.
Query Q−jDG for j=0,...,J−1 with JD<=q. A match gives k=jD±i, then verifies.
The disjoint queried blocks cover exactly the cyclic interval [−b,JD−b−1].
After ALL fail, Q'=Q−(JD−b)G has uniform scalar k' in [0,q−JD); recover
k=k'+JD−b mod q. This is paid information acquired on a full-range input,
not secret-range advice.

Convention for the exact count: each query includes its own identity check;
no earlier Q=O dispatch bypasses construction or queries. Then

    E[Nqueries] = sum_{j=0}^{J−1}(1−jD/q)
                = J−D J(J−1)/(2q).

If Q=O is dispatched first, the unconditional query expectation is smaller by
1/q for J>=1, and construction also has a reach probability. Do not mix these
conventions. Setting x=JD/q, the exact fixed-price query term is
cB[(q/D)(x−x²/2)+x/2].

The proposed continuous leading model replaces D by2b and drops bounded terms.
Assume fixed cB>0 per key and interval-backend expectation cK sqrt(L), cK>0:

    W(b,x)=cB b + A(x−x²/2) + C(1−x)^(3/2),
    A=cB q/(2b), C=cK sqrt(q).

Then W_x=sqrt(1−x)[A sqrt(1−x)−3C/2]. There is at most one interior critical
point, with W_xx=−A/2<0. Otherwise W is monotone. The minimum on [0,1] is an
endpoint; optimizing b cannot restore an interior advantage. At x=0 omit the
unused baby table, further improving that endpoint. The x=1 coverage endpoint
also faces the stronger existing interleaved baseline where memory permits.

This does NOT prove finite domination: D often does not divide q, so full
coverage needs a clipped final query. Floors, small residuals, batching, lookup,
backend initialization, translation to Q', materialization, exceptions and peak
memory matter. A nonnegative switch cost cannot improve the displayed model,
but comparator setup must also be matched. cK sqrt(L) is assumed, not proved.
No run is justified solely by this continuous switching rationale.

## Isolated IID cutoff restarts

For each trial choose independent uniform r, construct Q+rG and use fresh
solver randomness. Recover k by subtracting r and verify. Charge all sampling,
scalar multiplication, target-dependent setup and failed work. Shared unchanged
preprocessing must be explicitly separated; fixed declared PRNG seeds alone do
not establish IID uniform attempts.

With constant per-attempt initialization B>=0, subsequent runtime T, cutoff tau,
p=Pr(T<=tau)>0, mu=E[T]<infinity, and s=1−p, renewal gives

    W_tau = (B+E[min(T,tau)])/p.

When s>0 put m(tau)=E[T−tau | T>tau]. Then

    W_tau−(B+mu) = (s/p)[B+mu−m(tau)].

For assumed birthday survival S(t)=exp(−a t²), a>0,
S(tau+x)/S(tau)=exp(−a x²−2a tau x)<=S(x), so m(tau)<=mu.
Thus constant cutoffs do not improve this model even against B+mu. This says
nothing universal about heavy tails, retained work, informative observations,
varying cutoffs or actual EC walk laws. No residual heavy-tail mechanism beyond
competent cycle handling was identified by this proposal.

## Independent fixed-work portfolio

Assume independent blinded arms with leading survivors

    SR(t)=exp(−t²/(q cR²)),
    SB(t)=max(1−t²/(2q cB²),0),
    cR=5+s, cB=2.5+s, 0<=s<=1.

Here s is the S/M arithmetic price, unrelated to restart failure probability.
Since cR²−2cB²=12.5−s²>0, SB(t)<=SR(t). Their negative log survivors are
convex before the SB cutoff. For fixed total work w=x+y, convexity bounds
HR(x)+HB(y) by max(HR(w),HB(w))=HB(w). Hence independence gives

    SR(x) SB(y) >= SB(w).

Beyond the SB cutoff its survival is zero, so the comparison is trivial.
Integrating this inequality yields expected-work domination for predetermined
allocation schedules to which it applies at every budget. Informative internal
observations, actual stopping laws and hardware costs are not covered. Both
initializations, suspended states, terminal waste and summed memory remain paid;
the BSGS comparator must fit the SAME memory budget. Wall-clock speedup is not
automatically less total work.

## Sources, review and next decision

Known antecedents, not discoveries: [GWZ](https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf)
§§2–3 for signed/interleaved coverage; [Luby–Sinclair–Zuckerman](https://www.cs.utexas.edu/~diz/pubs/speedup.pdf)
§2 for IID restart scheduling. Proposer read these; root re-opened both and
checked the relevant coverage and renewal passages. The displayed candidate
calculus/convexity arguments were separately reviewed; neither source proves
the assumed EC/hardware models. Proposer's GPR full-text accesses failed and
its numerical constants were not used.

Retain no-survivor for these supplied premises, not a universal adaptive-search
exclusion. A next test needs an actual observable-dependent advantage, different
justified runtime law or finite full-cost margin. No restart tuning campaign
or generic Lean infrastructure is admitted. Root integrates; no Lean file/Audit
change. Current generic square-root reference and dashboard remain unchanged.
