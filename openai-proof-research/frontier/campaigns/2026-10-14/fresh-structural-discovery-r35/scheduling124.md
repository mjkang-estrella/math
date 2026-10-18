# Family 124: the fixed-capacity extension is technical

The full extension screened was exact deterministic minimum makespan scheduling of explicitly listed unit jobs under an arbitrary precedence DAG on **every fixed number m of identical machines**. No bounded height, width, special DAG class, or approximation promise was introduced. The source works with full schedules after independent padding, two rank frames, antichain boundaries, and globally defined Boolean predicates. Its main exact running-time exponent is large; a better exponent was not claimed.

The substantive source files `paper.tex`, `separators.tex`, `construction.tex`, `lists.tex`, `boundary.tex`, and `descriptions.tex` were read. The numerical occurrence of capacity three does not hide an additional argument: in `lists.tex`, Lemma `lem:list-length` assigns each surviving disjoint injection to a distinct job in a right boundary. A boundary of size m admits at most m such injections; root/switch initialization supplies at most two more entries. Thus the same proof gives list length at most m+2.

Here is explicit conservative accounting for replacing three by m throughout the same construction. The old-low extension uses at most 1+4(m+2)=4m+9 leaves. A switch entry adds three factors and a rank threshold, giving at most 4m+13. Same-direction trimming combines rank conditions and does not increase this allowance. A union of entries therefore has at most

    U(m)=(m+2)(4m+13)

leaves. The same-direction cutoff has at most U+1 leaves; the switched cutoff is constant size. Allow U+1 for either. The high and low child descriptions use at most U+2 and U+5, and their union at most 2U+7. Internal and reversed splits use at most U+7. All are bounded by

    K(m)=10(m+3)^2,

because K(m)−(2U(m)+7)=2m^2+18m+31>0. A larger K would make no conceptual difference. The construction and invariants are the source's unchanged operations with antichain m-sets in place of triples.

There are N^{O(m)} atomic predicates on N padded jobs, and Boolean expressions with at most K(m) leaves give at most 2^{O(K(m))}N^{O(mK(m))} descriptions. The source finite-state recursion scans a constant number of state combinations, evaluates explicit predicates, and decreases job-set size. With explicit job membership vectors its arithmetic and storage cost are polynomial in description length and N. This yields a deterministic **XP bound L^{O(m^3)}** including bit operations, after m<n and a trial horizon T≤n give N=mT≤n². For m≥n the longest-chain schedule is optimal and can be computed directly. Thus each fixed m is polynomial; no FPT dependence f(m)L^C is asserted. The constants here are a conservative transfer calculation, not an independently reviewed algorithm nomination.

Primary comparison: Nederlof–Swennenhuis–Węgrzycki, [A Subexponential Time Algorithm for Makespan Scheduling of Unit Jobs with Precedence Constraints](https://arxiv.org/abs/2312.03495), Definition 3.1 and Theorem 3.2, uses bounded-size separator timeslots. Its conflict-resolution proof moves ready non-sinks earlier and delays interchangeable sinks. Claim 4.1 reconstructs subproblem interiors from boundaries; §4.1 still permits large sink boundaries and counts subproblems by a threshold recursion. The stipulated source adds bounded global predicate descriptions and a fixed capacity injection count. Replacing three by m in that very count is already paid by the source mechanism. The broader headline does not make it a substantial new contribution.

Status: TECHNICAL; no count and no proposal. `checks.py` verifies the polynomial leaf inequalities, not the scheduling theorem.
