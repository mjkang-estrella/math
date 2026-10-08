# H027 oriented differential walks: reconciled detection scope

2026-10-08. Grok initial cards, separate Opus review, NEW native Astra review
of that review, and root algebra checks. Raw reports retained. No experiment,
new Lean claim or supported ECDLP gain. This file supersedes the raw review's
"all cards fail on paper" verdict.

## Accepted objections versus unsupported rejection

The fill F(P)=P+G is not negation-equivariant. A collision of x(P) and x(-P)
therefore need not propagate to a common distinguished endpoint. Opposite
distinguished visits can still yield a relation; later trails can meet.
"Never coalesce" is false as a universal assertion. Importing the negation-rho
constant is unjustified, but a full-group random-map constant is NOT thereby
a lower bound for this structured walk.

For a doubling bucket B with indicator A, the exact indegree is

    d(R)=1-A(R-G)+A(R/2),
    Var(d)=2*(|B|-|B intersect (2B-G)|)/q.

Root and Astra independently checked it, including coincident inverse images.
Tripling replaces2B-G by3B-G, for q!=3. Independence of the two membership
events is an extra assumption; visited bucket frequency also need not equal
uniform density. Neither variance nor its independence approximation establishes
the review's proposed collision-time law for these maps.

Thus5.09sqrt(q), the universal optimized-delta rejection and c<=3 gate are
UNVERIFIED HEURISTIC predictions, not paper falsifiers. The review read no
primary PDF for their application. Its theta*N²/(2q) endpoint estimate is
likewise a sampling model, not an exact law for correlated trajectories.
No lower bound for general coordinate-aware walks is accepted.

For Card2, different per-walker phases may prevent coalescence at equal points.
But stored equality still gives a relation; simultaneous equal points under
a shared global clock follow the same future schedule. Macro endpoint maps,
literal traversal and observed intermediate overlaps differ. Neither1/r
useful-hit probability nor r-fold time penalty is proved merely by phase state.

## Concrete rational repair of Card2

The proposed square-root recovery is unnecessary. Let G=(g,yG), and finite
oriented pair entries x(P),x(P-G). Put u=x(P)-g,v=x(P-G)-g,C=3g²+A_curve.
Then, with mu the slope through P and -G,

    u*v=C+2*yG*mu,
    mu=(u*v-C)/(2*yG),
    y(P)=mu*u-yG.

With prepared inverse(2*yG), recovery takes3M plus additions, no squaring or
Tonelli exponentiation. Root derived the identity from the curve equation and
the addition formula; Astra independently used the accepted H023/H024 identity.
Exceptional/infinity pairs require dispatch; yG!=0 for nonzero G of odd order.
This is an arithmetic repair using known project identities, NOT a new solver
or stopping-time argument. It also removes the review's supposed necessary
extra sign-testing evaluation.

## Contract gaps and disposition

Card1 invokes pure-G walkers absent from its operations. Null or duplicate
oriented trails need a charged retirement/restart policy. Powers2^e or3^e
repeat modulo multiplicative order: different integer depths do not guarantee
nonzero relation coefficient. Nonzero jump d_h alone does not prove O(1/q)
null frequency.

A full BSGS fallback violates the claimed low-memory envelope unless explicitly
declared; failed work still counts. Finite batches, starts, live walkers, actual
distinguished rule and visits, archived endpoints, tail work and caps all need
specification. A censored median versus an imported asymptotic constant cannot
demonstrate complete expected work. Neither raw proposed protocol is frozen
or admitted by this reconciliation.

Cards1/3 remain unvalidated dynamical hypotheses; Card2 has the rational repair
above. No numerical priority over the more concrete H028 provisional-key test
is justified yet. Reopening requires a full state/phase/detection/restart/memory/
failure contract and a positive matched complete-cost premise. Heuristic walk
predictions could then be tested, without presenting them as proven barriers.
