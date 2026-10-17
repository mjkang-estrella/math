# Family144: uniform subexponential derivative growth by retention

Myeongjin Kang; no affiliation. Original prose CC BY4.0; original code MIT. Pre-freeze technical screen, not a substantial nominee or independent proof verdict. Count unchanged. Source truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Exact imported interface

The pinned *A smooth three-torus diffeomorphism with simple Lebesgue spectrum* constructs a smooth standard-volume-preserving T on T³ and a real centered f whose bilateral Koopman orbit is an orthonormal basis of the entire centered L² space (thm:main). Section05 prop:stage permits each next admissible pair in every prescribed C∞ neighborhood of the previous map and inverse, with independently small L² vector change, a smaller bad arc, and a finite Laurent-polynomial prediction of one smooth test. Its complete proof and final diagonal argument have been read. Lower passage, signal and block operations are imported through this stated proposition; their complete proof bodies have not been read this round.

Every stage map is, in a global smooth volume-preserving coordinate system, the integrable twist S(θ,u,a)=(θ+φ(u),u,a), with φ a smooth real circle function. Section02 defines these coordinates as identifications of the entire physical torus, not local patches. Hence, for each fixed stage S_j, there exists C_j≥1 with

Γ(S_j,n):=max(1, ||D S_j^n||∞, ||D S_j^(−n)||∞) ≤ C_j(1+n), n≥1.   (1)

Indeed in twist coordinates the iterate has shear derivative Id+n φ'(u)E₁₂; the fixed coordinate map and its inverse contribute finite derivative factors. All norms here use the flat physical metric.

## Complete technical deduction

For any prescribed g:N→(0,∞) satisfying g(n)/n→∞, the source construction can be scheduled so that its final T additionally satisfies Γ(T,N_j)≤g(N_j) along an increasing sequence N_j, and

lim_(n→∞) log Γ(T,n)/n = 0.                                      (2)

After completing stage j, choose N_j>N_(j−1) so large that

2 C_j(1+N_j) ≤ g(N_j),   log(2 C_j(1+N_j))/N_j < 2^(−j).

At every later stage n>j impose the finitely many additional conditions

|Γ(S_n,N_j)−Γ(S_(n−1),N_j)| < 2^(j−n−1) C_j(1+N_j), 1≤j<n.       (3)

For a fixed iterate, Γ is continuous in the C¹ topology on the map and inverse. Each condition is therefore open and holds at the preceding map. Proposition stage permits their simultaneous imposition with all the source's convergence and prediction conditions. Those original conditions are retained unchanged, so the complete centered L² spectral conclusion still holds.

Smooth convergence and summation of (3) give Γ(T,N_j)≤(3/2)C_j(1+N_j), proving the asserted subsequence estimates. The sequence a_n=log Γ(T,n) is nonnegative and subadditive by the chain rule in both time directions. To avoid any hidden subsequence inference, fix N and write n=qN+r with 0≤r<N. Then a_n≤q a_N+max_(0≤r<N)a_r, so limsup a_n/n≤a_N/N. Apply this with N=N_j and send j→∞; nonnegativity proves (2).

For every ε>0 this also gives a finite C_ε with Γ(T,n)≤C_ε exp(εn) for all n. Every invariant Borel probability measure has all Lyapunov exponents zero: compact smoothness gives Oseledets integrability, the positive-iterate bound makes every exponent ≤0, and the inverse bound makes every exponent ≥0. This conclusion is for all invariant measures, not just standard volume.

The topological entropy is zero as well. An L-Lipschitz self-map of the three-torus has h_top≤3 log max(1,L): a sufficiently fine εL^(−n) covering controls n-step orbit distances, and the flat-torus covering number is O((L^n/ε)^3). Apply this to T^N and use h_top(T^N)=N h_top(T) to obtain h_top(T)≤3 log Γ(T,N)/N, then use (2). This elementary covering argument adds no new dynamical construction.

## Contribution boundary and unpaid stronger route

The earlier project proposal already rejected ordinary mixing, all-orders mixing, volume entropy zero and volume-almost-everywhere zero Lyapunov exponents as explicit source consequences. The all-invariant-measures conclusion above is a genuine extra quantifier relative to that displayed corollary, but its proof is finite-iterate retention followed by subadditivity. It is not nominated as a substantial new result under this campaign's explicit exclusion of routine robust transfers.

The closest operation comparison is Kunde, *Smooth zero-entropy diffeomorphisms with ergodic derivative extension*, Lemmas3.1–3.2 in the author manuscript. The complete Lemma3.2 proof chooses a new rotation increment after the conjugacy is fixed, preserves prescribed finitely many derivative-iterate observations, and sums future errors to retain them in the limit. That is the same retention operation used in (3). Kunde's different derivative-extension conclusion is not being transferred here. [Author manuscript](https://www.math.uni-hamburg.de/en/personen/kunde/ErgodicDiff.pdf).

A substantially stronger all-time prescribed growth bound Γ(T,n)≤g(n) is not proved. The constant C_j in (1) depends on a newly built chart; the next admissible large time depends on that constant. Retaining finitely many previously chosen times does not control the intervening range by a prescribed slow g. A quantitative relation between chart distortion, approximation accuracy and the next controlled time would be needed. This is a gap in this method, not an impossibility theorem.

Frączek's *Polynomial growth of the derivative for diffeomorphisms on tori*, Theorem7, does not rule out a mere polynomial upper bound: its actual hypothesis is uniform convergence of n^(−τ)Df^n to a nonzero C¹ matrix function. The exact definition and statement were read; its complete classification proof was not. Neither (1) for the varying stages nor a proposed upper bound supplies that nonzero limit. [Primary preprint](https://arxiv.org/abs/math/0205044v1).

The source whitening is only an L² operation: division by the square root of a spectral density and a measurable zero-set correction. The displayed flat vector already permits endpoint discontinuities. No smooth or bounded cyclic-generator upgrade, general-manifold gluing, all-time prescribed growth theorem, or substantial campaign result follows from this screen. These are not frozen substitute targets.
