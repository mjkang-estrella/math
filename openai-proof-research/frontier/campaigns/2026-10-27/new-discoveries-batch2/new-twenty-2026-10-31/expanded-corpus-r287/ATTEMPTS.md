# Ordinary routes and explicit exclusions

## 349036: noisy Nim, held

Read source Example 3, Bellman equation (5), Conjectures 9–10, and printed tables for k=4 through 10 (selected lines visible; not every table cell audited). For 0<p<1,
W_p(s,i)=p^{H(s,i)}(1-p)^{b-H(s,i)},
N_0=0, N_k=max_{0<=s<k} sum_{i<k} W_p(s,i)(1-N_i)/sum_{i<k} W_p(s,i).
At k=2^n, conditioning the leading output bit to zero leaves a full n-bit cube; its acceptance factor cancels. Also W_p(s,i)=W_{1-p}(2^n-1-s,i) on that cube. This DOES NOT imply N_{2^n}(p)=N_{2^n}(1-p), because lower-heap continuation values N_i(p) differ from N_i(1-p). For example the source exact N_3 formulas do not have that symmetry.

Route A: induct on n using cube complement and pairing i with 2^n-1-i. Missing: a sign inequality on paired continuation values, stable under the truncated lower-heap Bellman optimization. Neither pointwise monotonicity nor complement symmetry supplies it.
Route B: average transmitted moves uniformly. The output is then uniform on the cube, so some move wins with at least 1-(1/k)sum_{i<k}N_i. This proves the desired half bound only if sum N_i <= k/2. That proposed invariant is false: at p=1/5, N_0=0,N_1=1,N_2=4/5,N_3=7/10, whose sum is 5/2 > 2 for k=4. Thus this route fails, despite the desired power-of-two bound holding in the printed example.
Route C: try weighted prefix potentials using the reversible symmetric channel matrix. Need an inequality proving both a winning lower bound and the optimality of s=k-1 for p>=1/2. Positivity of the matrix for p<1/2 does not by itself control its signed continuation vector, and for p>1/2 the odd Fourier eigenvalues are negative. No full invariant obtained. Endpoint probabilities p=1 require special handling because retransmission can have zero acceptance probability; an endpoint convention alone would be an excluded correction. No computation/search was executed.

## 380048 and 380049: complete ordinary cyclic-ring reductions, zero nomination

Let R=F_2[x]/(x^p-1), J=sum_{i=0}^{p-1}x^i, a=r_N,b=r_Q, and h=a+b=J+1. The coefficient inner product is coefficient_0(u v^*), where *=x -> x^{-1}. Multiplication by J gives Ju=epsilon(u)J, J^2=J and h^2=h. The code is image u -> (au,bu).

If p=1 mod4 then a*=a,b*=b and epsilon(a)=epsilon(b)=0. Kernel of this map is exactly <J>: au=bu=0 implies hu=0, hence u=epsilon(u)J; conversely aJ=bJ=0. Thus dim C=p-1. Every coset has an even representative u (replace u by u+J); on the even subspace hu=u. The Gram operator of the map is a*a+b*b=a^2+b^2=h, so its restricted form is the standard inner product on even vectors. That restriction is nondegenerate since its orthogonal complement is <J> and epsilon(J)=1. Thus C intersects its orthogonal complement trivially and dimensions give C direct-sum Cperp=F_2^{2p}.

If p=3 mod4 then a*=b,b*=a, so the Gram operator vanishes. If au=bu=0, again u=epsilon(u)J; but now aJ=bJ=J, so u=0. Thus dim C=p and C is self-dual. This branch is already stated among known properties in Boston–Hao, section 2 (retained companion lines 77–146); it is not a new full-scope discovery.

For p=1 mod4, let w=(J,J) and sigma exchange the two coordinate blocks. The block-swap Gram operator a*b+b*a=0, hence sigma(C) is orthogonal to C. Also w is orthogonal to C and itself, because the component sums of all codewords vanish and 2p is even. The all-ones word w is not in C (each component of C is even, whereas J is odd), so C'=C+<w> has dimension p. Therefore sigma(C') is a p-dimensional subspace of (C')perp, hence equal. A coordinate permutation preserves weights, proving formal self-duality. The cosets C and w+C are disjoint, and adding w complements every bit, so the weight vector is A+A*. This completes the exact mathematical clauses of 380049.

These arguments use the source's ring construction, its dimension/parity observations and classical finite-dimensional orthogonality and coordinate-swap facts. Treat as a complete routine source bridge for triage, not a nominated significant new result. In addition the literature gate is incomplete: Joyner v1 returned HTTP 500 and is unread; the 2018 journal body and thesis are only partially read or not yet body-read as specified in the inventory. No worldwide-priority assertion, no CANDIDATE, no execution.

## 337518

See HELD-PROOF-337518.md for the sustained full ordinary proof, failed monomial and nonsingular shortcuts, exact semantic bridges, and dormant conditional Pi plan. This is the strongest surviving mathematical route, but source qualification is HOLD. Do not confuse its routine disconnected-domain correction with the connected theorem.
