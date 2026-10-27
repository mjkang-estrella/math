# All-order trace derivatives — already resolved by the author

MathDB355466 is stale: the source conjecture is already settled in the author's
posted2023 successor. Credit0; no new Lean/paper/acceptance proposed.

Original: Heinävaara2207.12812v1, Conjecture1.0.6p3. For Hermitian matrices,
a scalar function with nonnegative distributional kth derivative should retain
that positivity under t -> tr f(A+tB), with B positive semidefinite for odd k.
The source proves k3/4; matrices' Hermitian context is essential and is not to be
dropped just because the MathDB transcription abbreviates it.

Actual successor: Heinävaara2310.03227v1, Corollary1.2p1 and its proofp3, gives
ALL even k with no direction positivity restriction and all odd k with positive
semidefinite direction. The proof uses the positive tracial joint spectral
measure (Theorem1.4), nonnegative sums of truncated powers, and the half-plane
support lemma1.6. The following paragraph explicitly observes smoothness was
unnecessary. Both corollary and complete proof were read in actual PDF text and
rendered pages1,3, alongside the original conjecture page. Thus distributional
convexity is not an unaddressed residue. The interval-local version follows by
extending the positive derivative measure on a compact spectral neighbourhood
and integrating k times, or directly by the same local spline approximation.
Primary posted proof: https://arxiv.org/abs/2310.03227v1

Before locating the successor, search.py derived the exact source-Lemma2.2.3
sixth-derivative coefficient for A=diag(-2,-1,1), f(x)=max(x,0)^5. Its62-term
homogeneous polynomial is rational and the bounded search over80000 normalized
symmetric directions found no violation. This is finite uncredited evidence,
not a proof, and there is no reason to extend that search after reading the
actual all-order theorem. No new formal certificate is claimed for the search
or for the prior source theorem.
