# Sustained Bernstein analysis; no complete source result

The full endpoint is SCOUTING row1. Let hM=H^M and gM(d)=∫hM(t+d)h[M−2](t)dt, M≥2. Direct integration by parts gives

M²||G||²−||G′||²=M(M−1)Σ a_i a_j gM(λi−λj).

The source itself owns this reduction. Its Lemma4.1 displayed statement drops the positive factor that its proof correctly retains. This does not refute or change the inequality. No credit requested for this observation.

## Route A: constrained Gram matrix and exact-entry mechanism

For finite support N, form Kij=gM(|λi−λj|). Any finite increasing configuration satisfying all present M-step gaps extends to a doubly infinite one by placing additional points beyond either end with gaps≥π. Thus a NEGATIVE finite principal quadratic form would settle the literal source question, with no finite-to-infinite bridge remaining. Conversely positive sampled matrices establish nothing universal.

calculate.py samples160 configurations for each M=3,...,8, N=2M+3, using positive lognormal gaps rescaled by π divided by the minimum consecutive-M sum. Composite Simpson96 and Jacobi eigenvalues are exploratory. Floating arithmetic can place a minimum gap slightly belowπ; refine.py rescales using65-digit π before any interpretation. The first numpy/scipy implementation FAILED under the fixed512MiB address-space cap; no cap increase was attempted. Standard-library implementation used about12MiB groupRSS. The original failure remains documented.

Small apparent negatives disappeared under65-digit recomputation. refine.py computes every entry from the finite exponential expansion

gM(d)=2^(−2M+2) Re Σ[a=0..M,b=0..M−2] binom(M,a)binom(M−2,b) exp(i(M−2a)d) ∫[−π/2,π/2−d] exp(i(2M−2−2a−2b)t)dt

for0≤d<π, zero otherwise. The integral is a length for zero frequency and the exact exponential antiderivative otherwise. All six retained matrices have positive numerical minimum eigenvalues at65 digits. This is NOT interval arithmetic or a rigorous positivity certificate. Clustered near-coincident points explain poor conditioning. No counterexample survives these calculations.

## Route B: uniform Fourier and coalescence mechanism

The exact Fourier recurrence from hM″=−M²hM+M(M−1)h[M−2] is

hat(gM)(ω)=(M²−ω²)|hat(hM)(ω)|²/(M(M−1)).

It is negative on open sets with |ω|>M. Thus ordinary positive definiteness of gM on arbitrary configurations is FALSE. A proof via Bochner positivity cannot work; the gap condition is essential. This is a concrete structural obstruction, not a proposed resolution.

The opposite extreme, up to M points collapsing to one centre, also offers no obvious obstruction. After finite-difference changes of basis the limiting functions are hM,hM′,...,hM^(M−1). Their interior restrictions are trigonometric polynomials using only frequencies M,M−2,...,−M; each vanishes at the two support endpoints and its weak first derivative agrees with its interior derivative. On an interval of lengthπ these same-parity frequencies are orthogonal. Parseval therefore proves ||F′||²≤M²||F||² for every linear combination in this confluent limiting space. Translates of whole disjoint clusters add independently. This COMPLETE classical limiting bridge is uncredited and does not settle separated irregular clusters.

These two routes narrow the missing mechanism: prove positive semidefiniteness for every irregular configuration with at most M centres per lengthπ, despite a sign-changing Fourier transform. Source M=2 uses a nearest-neighbour square decomposition and g2(a)+g2(b)≤g2(0) when a+b≥π. At M≥3 additional bands and triangles occur; that identity no longer gives a full factorization. A spacing-aware banded Cholesky/Schur-complement invariant or a genuine sign-regularity theorem is needed. No such theorem is established here. Uniform-lattice or coalescence tests cannot substitute for it.

## Other completed mathematical triage (uncredited)

Scalar rotative maps: suppose a continuous fixed-point-free map f on a nonempty closed real interval satisfies |f^n(x)−x|≤a|f(x)−x| with a<n. The displacement has constant sign. Along an orbit the positive increments dk satisfy Σ[j=0..n−1]d[k+j]≤a dk. Summing k=0,...,N gives (n−a)Σ[k=0..N]dk≤Σ[j=0..n−2](n−1−j)dj, since the omitted upper-tail terms are nonnegative. The orbit converges in the closed interval; continuity gives a fixed point, a contradiction. Hence the all-n scalar extension is a routine orbit-summation adaptation; preserve but do not nominate it as a source-wide Banach-space result.

Discrete-Boole forward bridge: with simple roots αi separated by≥1, residues of p(x+1)/p(x) at αi are nonnegative; the rational function R=(p(x+1)−p(x))/p(x) is a sum Σci/(x−αi), ci≥0, Σci=n. Classical Boole's rational identity yields its positive-superlevel measure n/λ. The converse does not follow by reversing the residue calculation: cancelled poles, complex poles and multiple poles must first be ruled out. A large-λ tail coefficient alone cannot do this. No conjecture2.22 proof claimed.
