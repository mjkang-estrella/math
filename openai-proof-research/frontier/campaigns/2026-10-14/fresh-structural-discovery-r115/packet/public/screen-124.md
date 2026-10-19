# 124: multiplicities in a decision hierarchy

This prefreeze screen examined approximate counting/sampling of all feasible full three-job slots, not the previously investigated fixed-m makespan extension. For n=3T labeled unit jobs with a precedence DAG, the objects would be maps τ:J→{1,…,T}, with exactly three jobs in every slot and τ(x)<τ(y) for each precedence edge. Machines are not labeled within a slot. A count would count each map once. No FPRAS/sampler theorem, success quantifiers or complexity constants were frozen, since the required full counting operation was not obtained.

The stipulated source `thm:main` gives polynomial-time feasibility/minimum makespan (the displayed uniform bound is O(L^150020)). `lem:lex-prefix`, `lem:shared`, `cor:any-ideal`, the past/swap invariants, `lem:global-child`, `lem:relative-splits`, and the final global description bound give an existential normalized separator hierarchy. In the final DP, states (L,Z,R) and edges encode witnesses; an accepting path concatenates schedules. These are powerful proof operations, not merely a black-box feasibility oracle.

They nevertheless do not state that accepting paths correspond one-to-one to all original schedules. Normalization may change the schedule, and choices of hierarchy/marks may represent the same schedule more than once. Summing path weights therefore needs either a disjoint canonical decomposition with recoverable counts or a proved correction for encoding multiplicity. Neither was constructed here. Restricting to normalized schedules would change the objects and is not offered as a replacement.

The strongest primary normalization actually inspected was [arXiv2312.03495v1](https://arxiv.org/pdf/2312.03495v1), Theorem3.2 and Resolve-Conflicts proof. It moves ready nonsink jobs earlier and arranges sink jobs later to obtain proper separators without increasing makespan. It does not assert a uniform pushforward or recoverable multiplicity over all input schedules. v2 returned404; only v1 was used. Earlier r35's actual `scheduling124.md` and checkpoint were read: their fixed-machine list-size/XP accounting does not address this multiplicity question.

A concrete compatible-looking alternative also fails as a general sampler. Sample a uniform linear extension of the precedence poset and split it into consecutive triples; accept if every triple is an antichain. Every full feasible slot map has exactly (3!)^T linear extensions yielding it, so conditional uniformity is exact. The problem is the acceptance rate.

For three disjoint chains, each of length T, there is exactly one full feasible slot map: every slot contains the next job of each chain. The number of linear extensions is (3T)!/(T!)^3, while the number yielding that slot map is 6^T. Thus

    p_T = 6^T (T!)^3 / (3T)! = Θ(T (2/9)^T).

The equality counts interleavings of three internally ordered lists; the asymptotic follows directly from Stirling's formula. The rate is exponentially small although the instance is feasible and its full-slot map is unique. This excludes the unmodified rejection scheme, not approximate counting by another method, and does not prove hardness. No numerical test is being used as a mathematical gate.

A full result would need a globally multiplicity-correct use of the source hierarchy or another compatible counting mechanism with polynomially controlled probabilities. That operation remains missing. No weaker witness sampler or normalized-object count is nominated.
