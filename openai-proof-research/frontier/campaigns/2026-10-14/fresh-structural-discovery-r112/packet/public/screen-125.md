# 125: squared metric costs — no replacement drift certificate

This is a pre-freeze screen. It explored whether the source's improved clustering mechanism yields a new all-metric squared-cost approximation. No particular stronger factor was frozen, no full theorem was proved, and no method obstruction is offered as a nominee.

## Strongest existing compatible reduction

Byrka et al., [2604.06046v1](https://arxiv.org/pdf/2604.06046v1), explicitly develop power costs. Theorem 3.1 exposes the cost comparison required by their algorithm. Lemma 3.5 proves the general metric choice α=(3^p+1)/2 by a convexity argument. For p=2 this gives α=5, and satisfies the α≥2^p requirement of Theorem 6.1. Theorem 6.1's statement and setup were read, but its entire global analysis was not independently reread.

Crucially, exact facility budget is not an unpaid bridge. Appendix A was read in full: Theorem A.1, sparse-instance Lemma A.3, Algorithm 6, sparse repair Lemma A.4 and Algorithm 7, Claims A.6–A.7, and Corollary A.8. It turns a constant-additive pseudo-solution into an (α+ε)-approximation in n^{O((γp)^p αc/ε)} times the pseudo-solver's time. It guesses dense neighborhoods while retaining an optimum; sparsity bounds cheap deletions; if no cheap deletion is available, separated determined facilities give distinct optimum proxies and only a bounded exceptional set. Power costs are present in these inequalities themselves. The original Li–Svensson PDF was also retrieved, but not read; the proof relied on for this screen is the explicitly generalized appendix, not a citation to an unread original.

## The source operation that does not automatically transfer

Source125, `The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/build/sections/`, was read in `introduction.tex`, `preliminaries.tex`, the setup and positive-row formulation of `inequality.tex`, and the single-action potential and normalized comparison portions of `rounding.tex`. Its `thm:finite-inequality` is an actual finite certificate with normalized distances D, radii R, and directed parameters q. A key input is

R_i(1−P q_{ti}) ≤ D_i+D_t

on its specified q range. Its drift uses a linear combination of connection cost and the budget term, with an explicit surviving-cheap-client subtraction. The backup-client estimate is linear:

b_h ≤ d_i+(1−P_hat q_{hi})N_i.

Those are paid, precise operations. They are not a black-box certificate for arbitrary convex transformations of the objective.

Replacing every distance by its square does not meet the same assumptions. Even on the real line, with client j=0 and facilities i=−1,t=1, d(i,t)²=4 while d(i,j)²+d(t,j)²=2. The valid squared estimate has the form

R_i(1−Pq_{ti})² ≤ (sqrt(D_i)+sqrt(D_t))²,

under squared normalization, and the backup cost contains the mixed term 2d_i(1−P_hat q)N_i. The source's linear finite certificate does not bound these expressions by substitution. The example only diagnoses that substitution; it says nothing against the existence of a better squared-cost algorithm.

The `Single-Exponential-Recovery` companion's introduction and recovery contract were read. They assume a specific normalized metric instance, logarithmically many exceptional clusters, distinct proxies, and a total proxy-error budget. Together with the actual power-cost primary appendix, this prevents calling exact-budget repair or enumeration itself the novel step. It does not provide the missing squared-cost drift inequality.

## Exact unresolved operation and reading boundary

No finite inequality or coupled rounding potential was obtained that controls the mixed squared terms, retains the full all-metric scope, and yields a better approximation than the already compatible power-cost framework. No locality, Euclidean assumption, large-parameter limit, or additive-error surrogate was substituted. Because this central certificate remains missing, a broad headline about optimal squared-cost approximation was not frozen merely to create a target.

The source scalar certificate files and remainder of its finite inequality proof were retrieved but not completely semantically read. The companion's later recovery proof was not fully read. Accordingly this is a bounded compatibility screen, not an exhaustive proof that every possible integration is paid or impossible, and not worldwide priority clearance.
