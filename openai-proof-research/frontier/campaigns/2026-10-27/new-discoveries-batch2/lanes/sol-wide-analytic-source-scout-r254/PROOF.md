# Ordinary proof of Athreya–Mukherjee–Mukherjee Conjecture 2.4

Target: https://arxiv.org/pdf/2304.01145v2, pp4–6, Conjecture2.4. Fix integers 1≤s≤r, let n→∞, and replace at each step a uniform member of the current r-set by a uniform member of its complement. Let T be the number of rounds needed to see every s-set as a subset of a visited r-set. Then

E T ~ (r/s) binom(n,s)/binom(r,s) log binom(n,s).

All constants below may depend on the FIXED r,s. No assertion for growing r,s, limiting Gumbel law, or other replacement dynamics is made. This is a proposed full ordinary proof, not acceptance or a novelty certificate.

Write N=binom(n,s), p=binom(r,s)/N, q=sp/r. Count transitions starting with H_0; the source's round convention changes T by at most one. By permutation symmetry the distribution of T is identical for every deterministic initial r-set. Consequently we may start H_0 uniformly, the stationary reversible distribution.

## 1. A finite analytic chain, uniform in n

For a fixed set W of m≤2s distinguished coupons track B=H∩W, on the fixed state space E={B⊆W: |B|≤r}. For n≥m+r all these states exist. The transition probabilities are obtained as follows. From B, delete x∈B with probability 1/r for each such x, or delete an outside-W coupon with probability (r−|B|)/r. Independently choose an added coupon from the OLD complement of H: each y∈W\B has probability 1/(n−r), and a coupon outside W has total probability (n−m−r+|B|)/(n−r). Combine these choices to get B−x+y, B−x, B+y or B, respectively. Deleted distinguished coupons cannot immediately be reinserted.

The resulting matrix P(z), z=1/n, is analytic near z=0. At z=0 it only deletes distinguished coupons: each x∈B is removed with probability 1/r, otherwise B stays. Its unique closed class is ∅. Ordering states by cardinality gives eigenvalues 1−j/r on nonempty states of size j, and the simple eigenvalue1 at ∅.

Fix one target S of size s, or two distinct targets S,U of size s, and take W=S or W=S∪U. Let A be the states containing at least one target and D=E\A. Remove rows/columns of A, obtaining the substochastic matrix K(z). At z=0 deletion never enters A from D, so K(0) is stochastic, with right eigenvector 1, left eigenvector δ_∅ and simple eigenvalue1. All its other eigenvalues have modulus at most 1−1/r (if r=1 they are absent or zero).

Elementary finite-dimensional analytic perturbation therefore gives a simple real eigenvalue λ(z) near1 and a right eigenvector f(z)=1+O(z), normalized by f(∅)=1. The constants are uniform on this finite space. For completeness, choose a small circle enclosing1 but no other eigenvalue of K(0). The adjugate-over-determinant resolvent is analytic in z on this circle; its contour integral Π(z) is a rank-one analytic projection. Set f(z)=Π(z)1/[Π(z)1](∅). On a second circle |w|=ρ with 1−1/r<ρ<1, the complementary resolvent is uniformly bounded, hence K(z)^t=λ(z)^tΠ(z)+R_t(z) with ||R_t(z)||≤Cρ^t. This also proves the asserted O(z) controls without assuming a uniform eigenbasis or absence of Jordan blocks.

The stationary weight of B is π_n(B)=binom(n−m,r−|B|)/binom(n,r). In particular π_n(∅)=1−O(1/n). Multiplying the eigenvalue equation by π_n on D and using reversibility gives the EXACT identity

(1−λ) Σ_{B∈D}π_n(B)f(B) = Σ_{B∈D}π_n(B)P_n(B,A)f(B).

Since f=1+O(1/n) uniformly and π_n(A)=O(p), it follows that

1−λ = Q_n(D,A)(1+O(1/n)),

where Q_n is stationary one-step flow. Also the stationary survival probability, avoiding A at all times0,...,t, is

P(τ_A>t) = a_n λ^t + O(ρ^t),  a_n=1+O(1/n).

Here a_n=π_n|_D Π(z)1 tends to δ_∅ Π(0)1=1, analytically in z. All error constants are uniform over target choices: for a pair there are only s overlap types |S∩U|=0,...,s−1.

## 2. Exact escape rates for one and two targets

For one target, π(A)=p. From a state containing S, it is lost precisely when a member of S is deleted; it cannot be immediately readded. Thus Q(A,D)=ps/r=q, so 1−λ=q(1+O(1/n)).

For two distinct targets, put A_S={H:S⊆H}, A_U similarly. Their intersection has stationary mass O(n^{−s−1})=O(p/n), because |S∪U|≥s+1. The sum of their separate exit flows is 2q. The difference between this sum and the exit flow from their union is O(p/n): intersections contribute at most twice their stationary mass, and a transition from A_S\A_U to A_U\A_S must add a missing member of U. Its conditional probability is at most s/(n−r); the reverse direction has the same bound. Consequently the union exit flow is 2q+O(p/n)=2q(1+O(1/n)), since s/r is fixed positive. Therefore the pair chain has 1−λ_2=2q(1+O(1/n)).

## 3. The logarithmic-time lower bound

For fixed θ>0 and t= floor(θ log N/q), the preceding spectral expansions yield, uniformly in targets and distinct pairs,

P(S unseen through t)=N^{−θ}(1+o(1)),
P(S,U both unseen through t)=N^{−2θ}(1+o(1)).

Indeed t q/n=O(log n/n), t q²=O(q log n)=o(1), a_n=1+O(1/n), and the exponentially small ρ^t is negligible relative to either polynomial tail. This relative error at a growing logarithmic time is stronger than weak convergence to an exponential law at fixed rescaled times.

Take θ=1−ε with 0<ε<1 and let M_t be the number of unseen targets. Then E M_t=N^{ε}(1+o(1))→∞ and E[M_t(M_t−1)]/(E M_t)²→1. Hence Var(M_t)/(E M_t)²→0, so P(M_t=0)→0 by Chebyshev. Therefore liminf E T/(log N/q)≥1−ε. Let ε↓0.

## 4. The expectation upper bound, including the tail

The one-target estimate gives P(τ_S>t)≤C exp(−α_n t)+Cρ^t for all t≥0, where α_n=q(1−C'/n)>0 for sufficiently large n. Union bound gives P(T>t)≤min(1,CN exp(−α_n t)+CNρ^t). Sum this bound after t_0=ceil((log N+sqrt(log N))/α_n). The exponential tail contributes O(exp(−sqrt(log N))/α_n), and the ρ-tail contributes O(Nρ^{t_0}), both o(log N/q). Before t_0 use the bound1. Thus limsup E T/(log N/q)≤1. Together with Section3 this proves the literal conjecture for every fixed pair1≤s≤r.

## Eligibility boundary

The argument uses classical analytic perturbation, stationary flux, and a second moment. Its model-specific bridge is the fixed distinguished-union chain and the uniform pair escape rate. The source's iid missing-count proof and its r=s overlap recurrence are closest actual same-object bodies. Keller2012 and Abadi–Saussol2010 supply older general rare-event techniques; this proof does not establish that the present assembly is nonroutine under campaign rules. Current proof registries, published target version, and citing-body coverage remain uncleared. Do not count without independent source, proof, prior-art and substantive review.
