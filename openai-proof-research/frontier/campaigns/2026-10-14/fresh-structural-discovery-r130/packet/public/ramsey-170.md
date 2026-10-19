# Family 170: off-diagonal Ramsey numbers

This is a prefreeze screen. Nothing here is nominated, and no scope was frozen.

## Stipulated source contract (read in full)

Pinned source *Sharp Logarithmic Exponents for Fixed Off-Diagonal Ramsey Numbers*, `build/sections/00-introduction.tex` and `build/sections/06-conclusion.tex`:

- `intro:main`: for every fixed s>=6 there is C_s such that for every eps>0 and all large t, t^(s-1)/(log t)^(s-2+eps) <= r(s,t) <= C_s t^(s-1)/(log t)^(s-2).
- `intro:prime-construction`: for fixed d>=5 and 0<eta<1/10, for every large prime q with sigma=log q, there is a K_(d+1)-free graph on floor(q^d sigma) vertices with alpha < floor(q sigma^(1+eta)). The graph is the ordered incident-flag graph of an iid stream of flags of PG(d,q).
- The proof in `06-conclusion.tex` is by contradiction. It shows that SOME stream has no consistent k-tuple. Its invariants are stated to survive a bounded number of restrictions to events of probability bounded below (stream domination factor).
- `end:prime-interval` and `end:upper-bound` (an AKS-type upper bound via a uniform random independent set) transfer the prime construction to all t.

The companion *The Sharp Logarithmic Exponent of r(5,t)* covers s=5. Its introduction was keyword-searched only.

## Directions screened

1. **Inverse and chromatic conversions are paid by history.** The largest chromatic number of a K_s-free n-vertex graph, n^((s-2)/(s-1)) (log n)^(-(s-2)/(s-1)+o(1)), follows by inversion plus greedy colouring. Project `proposals/combinatorics.md` proposal C already derives it and labels it a routine translation. It also rejects "r(s+1,t)/r(s,t) -> infinity" as implied by Bradac's earlier bound. The i39 frozen note `F002-clique-free-edge-genus.md` uses the classical AKS upper bound, not the new construction. These are not reopened.

2. **Independence ratio in terms of maximum degree gives nothing new.** In the iid stream each pair of positions is adjacent with probability about 1/q, so typical degrees are about q^(d-1) sigma. Suppose the source argument is also restricted to the event that all degrees are within a constant factor of that value. The result would then be K_(d+1)-free graphs with alpha/n <= C (log Delta)^(1+eta)/Delta. The source's restriction clause (events of probability bounded below) appears to permit this, but I did not check it against the whole proof. However, random Delta-regular graphs of large girth already give alpha/n <= 2 (1+o(1)) log Delta/Delta for every forbidden clique. So the degree form of the construction is weaker than a classical bound and is not a candidate.

3. **s=4 is the wholly unbuilt central case.** Both pinned theorems require d>=4 (r(5,t)) or d>=5. The best bound recorded by the source is still Mattheus–Verstraete's Omega(t^3/(log t)^4) against the AKS upper bound O(t^3/(log t)^2). Settling the logarithmic exponent of r(4,t) would need the incidence/compression machinery to work in PG(3,q). The source makes no claim there. This is a famous headline whose central step is unbuilt, so the brief directs rounds away from it.

4. **Classical compilers were not pursued.** Feeding the new lower bound into a stepping-up lemma for hypergraph off-diagonal numbers, or into product constructions for multicolour off-diagonal numbers, would be a classical compiler application. No such lemma was read from its primary source in this round, and no sharp matching upper bound is available in those settings. Neither direction leaves an identified unpaid operation.

## Why this stops

Every consequence of the stated graph contract that I could formulate is either already in project history, weaker than a classical bound, or depends on the open s=4 construction. Removing the eps loss (a constant-factor lower bound) is the source's own explicitly unclaimed central step. No exact target was frozen.
