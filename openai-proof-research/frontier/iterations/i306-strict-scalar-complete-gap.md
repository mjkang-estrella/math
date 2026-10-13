# I306 — strict scalar versus complete norm gap for the six-dimensional example

2026-10-13. **Parent proof proposal; not independently reviewed or accepted.** This strengthens one explicitly open limitation in R019. It is not a new copy of R019's already accepted same-polynomial coefficient obstruction. Whether the stronger conclusion is substantial beyond R019 and known scalar equality operations requires a separate contribution decision. Thirteen findings remain accepted.

## Exact proposed theorem

Use the real matrix N from R019, with nonzero entries

    N12=6/5, N14=sqrt(14)/5, N23=8/5,
    N43=-3sqrt(14)/20, N45=5/4, N56=sqrt(2).

Let

    C_scalar(N)=sup{ ||p(N)|| : p scalar polynomial,
                                  max_|z|≤1 |p(z)|≤1 }.

Let C_complete use matrix polynomials of arbitrary finite coefficient size, with their matrix norm bounded by one on the disk. The proposed assertion is

    C_scalar(N)<2=C_complete(N).                 (G306)

The same scalar supremum is obtained over all scalar Schur functions on the open disk, evaluated by their first four Taylor coefficients. Thus the strict assertion concerns the supremum, not just nonattainment by each polynomial. No explicit numerical value or quantitative gap is claimed.

R019 already independently proves W(N)=closed unit disk, N^4=0, irreducibility, and an explicit 2-by-2 polynomial P with disk norm one and ||P[N]||=2. The stipulated complete-Crouzeix bound supplies C_complete≤2. For reference the directly computed power norms are

    ||N||²=(71+3sqrt(105))/32<4,
    ||N²||²=25/8,
    ||N³||²=7/4.

These values occur in the original I287 analysis, Section 10, and follow from its displayed height blocks. The first inequality also follows from sqrt(105)<19. All inner products and norms are complex Euclidean ones.

## 1. Compactness is made into a disk-algebra extremizer

Suppose for contradiction that C_scalar(N)=2. Choose disk-bounded polynomials p_j with ||p_j(N)|| tending to two. By the elementary compactness of bounded holomorphic functions (or diagonal compactness of their Taylor coefficients and uniform convergence on each smaller disk), pass to a Schur function f with coefficientwise convergence. Because N^4=0,

    p_j(N) → f(N)=sum_(k=0)^3 f_k N^k,

so ||f(N)||=2. This does not yet make f continuous on the closed disk.

Here is the needed finite interpolation step explicitly. If a Schur function g has |g(0)|<1, the Schwarz lemma applied after the disk automorphism gives a Schur function g_1 and

    g(z)=(gamma+z g_1(z))/(1+conjugate(gamma) z g_1(z)),
    gamma=g(0).

If |gamma|=1 then g is already a constant of unit modulus. Apply the recursion to f four times, unless such a constant terminates it earlier. In the nonterminating case replace the fourth remaining tail by any constant of unit modulus and reconstruct backwards. Each inverse Schur step preserves rational inner functions and adds at most one degree; its denominator has no zero on the closed disk since |gamma|<1. The resulting finite Blaschke product B is holomorphic on a neighborhood of the closed disk and differs from f by O(z^4). (An inverse step multiplies a difference of tails by z times an analytic nonvanishing factor.) Hence

    ||B||_disk=1, B(N)=f(N), ||B(N)||=2.

The same reasoning shows equality of the scalar polynomial and Schur-function suprema: any such rational B is uniformly approximable on the closed disk by polynomials; normalizing their suprema to at most one preserves the limiting evaluation. Only four coefficients matter. This step closes the previously unexcluded nonpolynomial-jet possibility without pretending that all extremizers are polynomials.

## 2. The zero order is forced; order one is impossible

Use the actual primary ACV v3 Proposition 11.9, whose proof is given in the same section: a scalar disk-algebra f attaining factor two has a zero at an eigenvalue of its matrix. Its proof obtains a zero Jordan block of size two for f(A), then applies the elementary Jordan-block composition rule. N has only the eigenvalue zero. Therefore B(0)=0.

If B'(0) is nonzero, formal inversion at zero modulo z^4 gives a polynomial q with q(B(N))=N; equivalently alg(B(N))=alg(N). ACV v3 Theorem 11.7 now applies with Ω=unit disk. Its conclusion is that B is a disk rotation. Here the theorem's center is necessarily zero because zero is the only eigenvalue, and its disk radius is one. Thus ||B(N)||=||N||<2, a contradiction.

For clarity, the primary theorem's mechanism is also explicit: its sharp square-function equality yields a reducing two-dimensional nilpotent block of norm two for B(N); polynomial inversion transfers this reducing subspace to N. On that subspace N=q(0)I+q'(0)J. Numerical radius at most one and equality in Schwarz's lemma force the disk-rotation alternative. The proposed proof invokes the primary theorem with its exact disk-algebra and algebra-generation hypotheses, not a polynomial-only rigidity assertion.

## 3. Higher zero orders have an explicit norm bound

If B has zero order at least two, write B(z)=z²g(z), where g is Schur by repeated Schwarz's lemma. Put a=|g(0)| in [0,1]. Schwarz–Pick at zero gives |g'(0)|≤1-a². Since N^4=0,

    B(N)=g(0)N²+g'(0)N³.

Consequently

    ||B(N)||≤a sqrt(25/8)+(1-a²)sqrt(7)/2
             ≤sqrt(7)/2 + (25/8)/(4 sqrt(7)/2)
             =81/(16 sqrt(7))<2.

The middle bound is the unrestricted maximum of a concave quadratic, so it is valid on [0,1]. The strict final inequality follows by squaring: 6561<7168. This includes orders three and above; for order at least four B(N)=0. It contradicts ||B(N)||=2 in every remaining case.

Thus no Schur-jet extremizer has norm two, while the compactness/interpolation argument would supply one if the scalar supremum were two. This proves the proposed strict supremum gap. It does not compute its size. Complete equality still comes from the already verified R019 polynomial.

## Dependencies and contribution boundary

The pinned complete upper bound is assumed true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. R019's algebra and power norms are existing checked ingredients; its earlier acceptance must not be counted again. New downstream steps here are compact Schur-jet extremization, the order-one/higher-order split, and their combination to separate the scalar and complete constants of this specific matrix.

Primary external source actually read: *Square Functions, Complete Crouzeix Conjecture in Dimension Three, and the Clouâtre–Ostermann–Ransford conjecture*, arXiv:2608.27346v3, https://arxiv.org/html/2608.27346v3. Current web-rendered Section 11 was read at lines 1935–2118, including the complete statements and proofs of Proposition 11.1, Lemma 11.6, Theorem 11.7 and Proposition 11.9. Their earlier square-function machinery is relied on through the stated theorem; it has not been independently re-proved here. The finite Schur recursion and Schwarz–Pick step above are elementary displayed deductions. No new full paper or section copy is retained.

This assertion settles a genuinely stronger question than whether constant coefficient compressions of the particular P attain its norm. Nonetheless, the proof uses established ACV equality theorems and two already computed power norms, so a TECHNICAL contribution verdict is a serious possibility. No minimal counterexample dimension, uniform perturbation gap, unbounded coefficient-rank hierarchy or worldwide priority is claimed.
