# Technical operations and failed bridges

This is support for a no-nominee screen, not a proof of the full target.

## 1. A paid signed-scale consequence

Use exactly the odd Gevrey function φ and localizing W from086 `outer.tex` and put

    A_a(f)(x)=∫ a^{-1} φ⁽⁴⁾(t/a) ∏_{j=1}³ f_j(x+jt) dt.

For every bounded measurable scalar b(a), |b|≤1, supported in a compact positive scale interval,

    || ∫ b(a) A_a(f) da/a ||_1 ≤ C ∏_j ||f_j||_3.                 (1)

Proof: pair with one compactly supported bounded g(x). Write a=u2^n, 1≤u<2, as in the source. At fixed u multiply each admissible kernel in the source's reconstruction by b(u2^n). Absolute values at the level of scalar cell forms bound this by the same local-absolute sum; a modulus≤1 coefficient costs nothing. The bounded multiplicity of translates and shifted lattices is exactly the source's. Integrate du/u and use its L³ maximal-function estimate. On this finite scale interval the integrals are absolutely convergent for bounded compact inputs, so all rearrangements are justified. Duality proves (1), followed by density. This repeats a source operation rather than creating a new one.

For any *fixed* disjoint measurable scale sets E_k contained in a compact interval, put U_k=∫_{E_k} A_a da/a. Apply (1) to b=Σ ε_k1_{E_k}, with independent Rademacher signs. Complex Khintchine and Tonelli give

    ||(Σ|U_k|²)^{1/2}||_1 ≤ C′∏||f_j||_3.                       (2)

The sets in (2) are independent of x. Randomization does not make them output-dependent.

## 2. What binary decomposition really yields

Let u_n=∫_{2^n}^{2^{n+1}} A_a da/a over N consecutive scales, padded by zeros to N=2^L. Write S_k=Σ_{n<k}u_n. For a partition of the index interval, decompose each increment interval into maximal dyadic blocks. At each dyadic length there are at most two blocks per increment, and all blocks across different increments are disjoint. If U_B=Σ_{n∈B}u_n, Minkowski in ℓ^r, followed by ℓ^r≤ℓ² for r≥2, gives pointwise

    V^r(S_k) ≤ √2 Σ_{ell=0}^L (Σ_{B of length 2^ell}|U_B|²)^{1/2}. (3)

For a fixed ell the blocks correspond to disjoint scale intervals, so (2) integrates each square function. Thus

    ||V^r(S_k)||_1 ≤ C(1+log(2N))∏||f_j||_3.                    (4)

The partition can depend on x in (3), but the right side paid for all levels. Equation(4) is a finite-scale smooth-model bound only. Taking N→∞ loses control. There is no deduction here of failure, sharpness of the logarithm, or nonexistence of a better argument.

A basic negative control prevents a false pointwise shortcut: u_n=1 gives V^r(S)=N whereas (Σ|u_n|²)^{1/2}=√N. This is only a scalar-sequence counterexample to the proposed pointwise inequality, not a trilinear-transform counterexample. The source's unconditional bound is stronger than a pointwise square-sum hypothesis and is not contradicted by this example.

## 3. Exact anchor cancellation calculation

Set D_j=∂_t−j∂_x and w=D_0D_1D_2D_3 ψ for a smooth compact Gevrey ψ supported strictly inside an admissible cell's progression region. Each marginal ∫w(u−jt,t)dt vanishes by integration by parts. In the convention with differentiation symbol iξ, write

    ŵ(ξ,τ)=P(ξ,τ) ψ̂(ξ,τ),  P(ξ,τ)=∏_{j=0}³(τ−jξ),

since i⁴=1. Multiplication by e^{ix} changes this to

    ŵ_mask(ξ,τ)=P(ξ−1,τ) ψ̂(ξ−1,τ).

At ξ=5 and τ=5j, the polynomial factors are 0,105,−240,3465 for j=0,1,2,3, respectively. Choose ψ nonnegative, even and supported in a sufficiently small neighborhood of an interior point so its Fourier transform is nonzero at these finitely many frequencies (translation only changes phase). Then the three nonoutput marginals really are nonzero. The output marginal remains zero. This is a genuine witness that the admissible class is not closed under even a smooth output mask.

This calculation does **not** prohibit absorbing one common mask into a common input. The target's difficulty is a family m_a(x) that changes with a. The source bound is not stated for a different fourth input at every cell. Sharp masks add a separate derivative-bound problem. Smoothing them without quantified constants is not a repair.

## 4. Compression is uniform in depth, not in arbitrary pathwise complexity

The source's column system has a common budget D with Σ_v1_{J_v}(x)≤D, and `lem:compression` bounds m inherited projection factors by

    [C(m+1)^C log(2D)]^{C(m+1)} ||z||_2.

If one literally installs M unrelated candidate masks as M columns born at the root, D≥M. They are counted even when only one is selected. Thus the stated estimate gives a positive power of log M, not a constant independent of the menu. No claim is made that every encoding must have M columns. Exploiting pointwise disjointness and a bounded number of switches is precisely the unproved compression/energy work.

## 5. Why the two existing variation proofs do not close this gap

In the Walsh bilinear paper, the exact identity expresses a truncated lacunary-tree wave-packet sum as a modulated dyadic conditional expectation of its full sum. Lépingle then handles all output-dependent stopping indices. The source086 has inherited projections and quadratic modes, but their compression estimate alone neither identifies scale truncation with a conditional expectation nor gives this variational bound. A variable top phase cannot be silently treated as a fixed martingale modulation.

In the triangular companion, entrywise switches of the dual array have total variation≤2n times its original modulus. The mixed energy jumps contain its norm at least twice; after integration the cost is Σn_v³+n(n_0³+n_0²(n_1+n_2)). Normalizing n_0=n^{-1/2}, n_1=n_2=1 gives an O(1) energy and hence a √n form bound. That operation is actually read in full and credited to the companion. It is not a four-input estimate with norms (∞,3,3,3). A valid representation and jump functional for the latter are absent.

The 2026 shifted-bilinear proof uses V^2 of the sequence of **individual mean-zero averages**≤Cℓ² of those averages. Our smooth truncated singular integral is a sequence of **partial sums** of scale pieces, so this elementary inequality does not apply to it; (3) describes the actual cost. Their smooth averaging variation is an additional black-box input. The hard-error upgrade would still need new trilinear shifted-kernel bounds with quantified translation costs, and the output exponent1 requires the p<2 continuous-square-function treatment.

All these failures are failures of specified arguments. None is a counterexample to the unchanged full annular target.
