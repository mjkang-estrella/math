# Bernstein square-sum convexity via finite Fourier averaging

Let b_(n,k)(x)=choose(n,k)x^k(1−x)^(n−k) and φ_n(x)=∑_(k=0)^n b_(n,k)(x)². The target is convexity on[0,1] for every natural n. We prove it on all real x.

Put N=n+1 and let ζ_j=exp(2πij/N). Finite geometric-series orthogonality gives ∑_j ζ_j^k conjugate(ζ_j^l)=N when k=l and0 otherwise for0≤k,l<N. Expanding the squared norm of ∑_k a_k ζ_j^k and summing over j therefore gives N∑_k a_k² for arbitrary real coefficients a_k. This is finite Parseval; there is no convergence or integration issue.

By the binomial theorem, ∑_k b_(n,k)(x)ζ_j^k=(1−x+xζ_j)^n. Hence

φ_n(x)=(1/(n+1))∑_(j=0)^n |1−x+xζ_j|^(2n).

Each summand is convex: a norm composed with a real affine map is convex, and its nonnegative values can be raised to the nonnegative integer power2n while preserving convexity. The case n=0 is constant. A positive finite average is convex, proving the full conjecture.

Reindexing k↦n−k gives symmetry φ_n(1−x)=φ_n(x). Convexity applied to the midpoint of x and1−x proves φ_n(1/2)≤φ_n(x). Convexity together with this minimum proves monotonicity on either side of1/2. At the midpoint, b_(n,k)(1/2)=2^(−n)choose(n,k); Vandermonde's identity gives φ_n(1/2)=4^(−n)choose(2n,n).

## Formal coverage

`character_orthogonality` uses the primitive standard character on ZMod(n+1) and proves distinct frequencies do not alias. `finite_parseval` sums the exact complex expansion. `binomial_fourier` and `finite_average_identity` prove the bridge from the original defining polynomial, not an alternative assumed representation. `bernstein_square_sum_convex` states precisely the expanded source formula on[0,1], while `convexOn_univ` proves its stronger global version. All shape corollaries and the sharp minimum are also certified.

## Prior status

Gonska, Raşa and Rusu, arXiv1401.7908v1, Conjecture3.2, is the source target. Nikolov's arXiv1402.6539v1 Corollary4 already proves this convexity theorem. A Parseval-based proof was published by Gavrea and Ivan in2014. The original source already proves the minimum in Lemma3.5. We claim full local formal verification, not discovery or first formalization. Related MathDB327181/327182 are not counted separately. The paper also derives a positive coefficient expansion by a different integral argument; that extra identity is explicitly not part of the Lean certificate and is unnecessary for the certified outcome.
