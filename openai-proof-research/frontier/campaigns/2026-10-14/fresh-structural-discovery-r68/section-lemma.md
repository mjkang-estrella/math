# Homogeneous biased-cube sections: author support lemma

Status: complete author proof, no independent review, no standalone substantial nomination. This was derived after exploratory messages from the parent suggesting circuit/matroid reduction. That assistance and the parent's subsequent check are author collaboration, not independent gates. No full higher-corank target is frozen or proved.

For p in(0,1), q=1−p, let independent signs ε_i have P(ε_i=1)=p. For every real matrix A of rank k with n columns,

    P(Aε=0) ≤ f(k+1),     f(t)=p^t+q^t.

The same bound holds for any homogeneous codimension-k subspace. If n≥k+1 it is attained by requiring k+1 coordinates to be equal and leaving all others free. For k=n the event is empty, and the displayed bound is not asserted sharp at that dimension. Rank0 gives equality1=f(1).

## Circuit contraction proof

Induct on k. Ignore zero columns. If k>0 and the nonzero columns are independent, their signed sum cannot vanish, so the event is empty. Otherwise select a minimally dependent set C of nonzero columns. Its size ℓ≥2 is at most k+1; its rank is r=ℓ−1; its one-dimensional kernel has no zero coordinate.

Condition on every sign outside C. A solution on C lies in an affine line with direction having no zero coordinate. Such a line meets {−1,1}^ℓ in at most two points, since any one coordinate determines its line parameter. If it meets in two, every coordinate differs, so those two points are antipodal. If one has a positive signs, their total probability is p^a q^(ℓ−a)+p^(ℓ−a)q^a≤p^ℓ+q^ℓ. To see the inequality, assume p≤q and write z=p/q≤1; then z^a+z^(ℓ−a)≤1+z^ℓ, because (1−z^a)(1−z^(ℓ−a))≥0. A single point has probability at most max(p,q)^ℓ≤f(ℓ). Empty fibers cost zero.

Additionally, outside signs must have sum zero in the quotient of the column span by span(C). The projected remaining columns have rank k−r. This is still a homogeneous equation, unlike the conditional equation on C. The inductive bound and independence give

    P(Aε=0) ≤ f(r+1) f(k−r+1).

For a,b≥1,

    f(a+b−1)−f(a)f(b)
      = pq (p^(a−1)−q^(a−1))(p^(b−1)−q^(b−1)) ≥0.

Thus the last bound is at most f(k+1). This includes k−r=0, where f(1)=1. The conditional affine-fiber estimate is obtained from the entire circuit, not from an unjustified homogeneous estimate on translated sections.

## Exact extremizers away from the fair law

Suppose k≥1 and p≠q. If equality holds, a chosen circuit cannot have r<k: both factors in the displayed difference are then nonzero with equal signs, giving a strict inequality. Therefore the circuit spans rank k and has ℓ=k+1.

Attaining f(ℓ) requires every outside-sign configuration (all have positive probability) to have a two-point circuit fiber whose points are the all-plus and all-minus assignments. A mixed-sign antipodal pair has strictly smaller mass, as follows from the preceding product identity with 0<a<ℓ; a singleton is also strictly smaller. Hence the circuit columns sum to zero and the outside signed sum is zero for every configuration. Flipping one outside sign shows that each outside column is zero. The circuit kernel is the span of the all-ones vector. Conversely these conditions give exactly equality. Consequently, as a subspace of R^n, every extremizer is one equality block of k+1 coordinates and otherwise free coordinates. No analogous uniqueness is asserted for p=q.

## An explicit nonoptimal uniform gap

Fix k≥1 and p≠1/2, and put u=min(p,q), v=max(p,q), ℓ=k+1. Define

    gℓ=max(v^ℓ, max_{1≤a≤ℓ−1}[u^a v^(ℓ−a)+u^(ℓ−a)v^a]),
    M=max({ f(r+1)f(k−r+1):1≤r<k }
          ∪ {gℓ, v^ℓ+u^ℓ f(2)}).

The first set is empty for k=1. Every listed value is strictly below f(k+1), so δ=f(k+1)−M>0. Any nonextremal rank-k homogeneous section has probability at most f(k+1)−δ.

Indeed, a nonspanning circuit gives the first bound. If a spanning circuit's kernel is not the all-ones line, any antipodal pair is mixed and any other fiber has at most one point, giving gℓ. If its kernel is the all-ones line but some outside column is nonzero, let S be the outside signed sum. Its zero event has probability at most f(2), by the proved theorem at its positive rank and the monotonicity of f. When S=0 the circuit fiber costs f(ℓ); when S≠0 it has at most one point (an antipodal pair would force target zero), so costs at most v^ℓ. Thus total probability ≤v^ℓ+u^ℓ f(2). Independent nonzero columns give the empty event. This gap is not claimed optimal, and it concerns exact sections, not a dimension-free small-ball neighborhood.

## Limits and actual comparison

Jain–Sah–Sawhney, arXiv2103.02467v1, introduction and §2.3 were actually read (local extracted lines1–365 includes §2.4 statement/remark). Lemma2.5 proves a dimension-free small-ball bound (1−p)^k for orthonormal projections of Bernoulli(0/1) variables, using Rogozin and restricted invertibility. It is an affine concentration statement after conversion to signs, and does not imply the stronger homogeneous zero-atom bound above. Their Conjecture1.2 already predicts the higher-corank base p^(k+1)+q^(k+1) for independent biased signs. The present lemma is necessary for that conjecture, since forcing every row into one violating fixed section, extended by free coordinates, would violate its asymptotic bound. It does not prove that conjecture: union over random kernel subspaces and small-ball estimates remain separate issues.

Bounded web searches for sharp biased homogeneous section bounds and circuit Littlewood–Offord estimates did not locate an exact matching primary. This is not a literature-priority conclusion. No full review or nomination is requested for a short source-independent lemma alone.

Additional primary comparison: Singhal1912.02886v2 introduction and complete §2 (extracted1–334) were read. Its scalar arbitrary-center concentration optimum uses convex decomposition of positive/negative subset-sum profiles. This is credited as the closest inspected sharp biased scalar operation; no arbitrary-codimension consequence is attributed to it. Exact PDF/text hashes are in primary-section-receipt.json.
