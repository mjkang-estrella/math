# I307 — spectral support of scalar disk extremizers

2026-10-13. **Unreviewed parent proof proposal.** No independent proof, contribution or acceptance verdict. This gives a stronger general route to the proposed I306 scalar/complete separation. I306 and this generalization must not be counted as separate findings if accepted as one package. The existing R019 acceptance is unchanged.

## Proposed theorem

Let A be a finite complex matrix with numerical radius at most one and spectrum strictly inside the unit disk. Let f be any holomorphic Schur function on the open disk, evaluated at A by its convergent Taylor functional calculus. Suppose ||f(A)||=2. Let ν_λ be the largest Jordan-block size of A at λ. Then zero is an eigenvalue with ν_0≥2, and

    f(z)=η z^r product_(λ in σ(A), λ≠0)
                    [(z-λ)/(1-conjugate(λ)z)]^(k_λ),       (E307)

where |η|=1, 1≤r≤ν_0-1 and 0≤k_λ≤ν_λ. Thus every nonzero zero of the extremizer is an eigenvalue, and every nonzero pole is the reciprocal conjugate of an eigenvalue. The theorem is a necessary condition, not a sufficiency claim for every listed product.

In particular, if A is nilpotent of index L, every factor-two Schur extremizer is ηz^r for 1≤r<L. Moreover the scalar disk functional-calculus constant equals two if and only if ||A^r||=2 for some 1≤r<L. This includes a supremum statement over all scalar polynomials or Schur functions. If every such power has norm strictly below two, the scalar supremum is strictly below two.

For R019's N, the power norms in I306 therefore give C_scalar(N)<2=C_complete(N), without invoking ACV's algebra-generation theorem. That is a consequence of the present proposed theorem, not another independent nomination.

## 1. Scalar Hardy-space version of the source argument

Choose unit singular vectors x,y with f(A)x=2y and f(A)*y=2x. Define

    R(z)=(I-zA)^(-1), P(z)=x*R(z)x, Q(z)=y*R(z)y,
    M(z)=y*R(z)x, L(z)=x*R(z)y,
    a²=sum_(k≥0) |y*A^k x|².

All these resolvent series converge absolutely beyond the closed disk because σ(A) is strictly inside it. In particular a is finite. Write m_k=y*A^k x, p_k=x*A^k x and similarly for q_k,l_k. The constant diagonal coefficients satisfy p_0=q_0=1, and l_0=conjugate(m_0).

For any polynomial g, the ordered products and the singular pair give

    2 x*g(A)x = y*(fg)(A)x,
    2 y*g(A)y = y*(gf)(A)x.

For any bounded analytic h, the coefficient pairing is y*h(A)x=sum_k h_k m_k. The series converges absolutely and Cauchy–Schwarz bounds it by a||h||_H². Multiplication by the Schur function f is a contraction of H²; this follows by integrating |f(rz)g(rz)|²≤|g(rz)|² on circles and taking r upward to one. Therefore

    |x*g(A)x|≤(a/2)||g||_H²,
    |y*g(A)y|≤(a/2)||g||_H².

Testing against finite conjugate coefficient arrays and passing to the limit yields

    sum_k |p_k|²≤a²/4, sum_k |q_k|²≤a²/4.

In particular a²≥4. This is the disk-specific unweighted estimate; the general-domain Faber estimate in the source uses weaker weights. No boundary continuity of f has been assumed.

## 2. Equality of the positive resolvent blocks

For |z|=1,

    (I-zA)*(R+R*)(I-zA)=2I-zA-conjugate(z)A* ≥0,

so H=R+R* is positive. Compress by [x,y] and write its scalar diagonal entries as D_x=P+conjugate(P), D_y=Q+conjugate(Q), with cross entry C=M+conjugate(L). Positivity gives 2|C|²≤D_x²+D_y² pointwise. Parseval gives

    integral D_x² = 2+2 sum_k |p_k|² ≤2+a²/2,
    integral D_y² ≤2+a²/2,
    integral |C|² = a²+3|m_0|²+sum_(k≥1)|l_k|² ≥a².

Thus 2a²≤4+a², or a²≤4. Equality with the preceding lower bound forces all of the following:

    a²=4; p_k=q_k=0 for k≥1;
    m_0=0; l_k=0 for every k;
    D_x=D_y=2; |M(z)|=2 on the unit circle.

For the last assertion, the first equalities reduce the positive compression to [[2,conjugate(M)],[M,2]], so |M|≤2. Its squared integral is exactly four. Continuity makes its modulus exactly two at every point. These are identities in the original matrix and its original resolvent.

The equality 2=y*f(A)x=sum f_k m_k, together with a=2 and ||f||_H²≤1, is equality in Cauchy–Schwarz. Hence

    f_k=conjugate(m_k)/2 for every k,
    f(z)=(1/2) x*(I-zA*)^(-1)y.                 (R307)

In particular f is rational, holomorphic on a neighborhood of the closed disk, inner on the circle, and f(0)=0. The phase is fixed by the chosen singular-pair convention. This establishes the rational conclusion directly even though the original f was only a Schur function on the open disk.

## 3. Locate the zeros and bound their multiplicities

Let ℓ be the degree of the minimal polynomial μ_A and put

    q(z)=product_(λ in σ(A)) (1-conjugate(λ)z)^(ν_λ).

The resolvent of A* has a matrix numerator of degree at most ℓ-1 over q(z), by the minimal-polynomial resolvent identity. Factors for λ=0 are constant one; thus deg q=ℓ-ν_0 when zero belongs to the spectrum, and deg q=ℓ otherwise. Equation (R307) has the same scalar denominator, before cancellations, with numerator degree at most ℓ-1.

A nonconstant rational function holomorphic near the closed disk and of modulus one on its circle is a finite Blaschke product: divide by the factors of its finitely many disk zeros; both the quotient and its reciprocal are holomorphic and have unit boundary modulus, so the maximum principle makes the quotient constant. Every nonzero Blaschke zero α produces an uncancelled pole at 1/conjugate(α). Such poles of (R307) must lie among the zeros of q, with multiplicity at most ν_λ. Consequently α is an eigenvalue λ and its multiplicity k_λ is at most ν_λ.

Let K=sum_(λ≠0) k_λ and let r≥1 be the zero multiplicity at zero. After cancellation the numerator degree is r+K and the denominator degree is K. Restoring the cancelled factors of q gives a numerator of degree

    r+K+(ℓ-ν_0-K)=r+ℓ-ν_0.

It is at most ℓ-1. Hence r≤ν_0-1. If zero were absent, this inequality would read r≤-1, impossible; if ν_0=1 it would read r≤0, also impossible. This proves (E307) and the asserted necessary spectral restrictions. No converse for arbitrary Blaschke products is inferred.

## 4. Nilpotent supremum criterion

For nilpotent A, equation (R307) is a polynomial, so its innerness makes f a monomial of degree between one and L-1. It follows that a norm-two Schur function exists exactly when some power A^r has norm two.

To treat a supremum, a sequence of Schur functions with evaluations tending to two has a coefficientwise convergent subsequence, defining another Schur function by uniform convergence on each smaller disk. Nilpotent evaluation uses only L coefficients and is continuous in them, so the limit attains two. Scalar polynomials and Schur functions have the same evaluation supremum: replace h(z) by h(tz), t<1, approximate by its uniformly convergent Taylor polynomials on the closed disk, normalize by their disk norms, and then let t increase to one. The stipulated scalar constant-two bound controls this common supremum. This proves the iff criterion and its strict alternative.

For the explicit N, none of the three nonzero powers has norm two, while R019's matrix polynomial does attain two. Thus the proposed I306 conclusion follows. A classical Crabb power-equality theorem could translate ||A^r||=2 into a reducing weighted-shift block, but that optional reformulation is not a premise or separate finding here.

## Source and novelty limits

This proof adapts the ordered-test/positive-resolvent argument in the actual pinned *A direct proof of the complete Crouzeix inequality*, `thm:domain`, `eq:crossfunctional`, `eq:ordered-products`, `eq:weighted-dual`, `eq:diagonal-L2`, and `eq:cross-L2`. The parent read the corresponding original TeX lines 315–450, together with `thm:main` at lines 30–95. On the disk, the Taylor/Hardy coefficient norm has exact unweighted Parseval, which is the additional equality extraction here. The numerical-radius positivity congruence is displayed above; no upstream proof truth is audited.

The prior primary ACV v3 Section 11 supplies polynomial equality rigidity and a weaker eigenvalue-zero obstruction; I306 records the exact reading. Its general extremal-function machinery is not needed in this proof. The external search also found the Berger–Stampfli mapping theorem and Crabb power-equality literature, but no complete comparison with their equality statements has yet been performed. Those are required contribution-review leads, not evidence of novelty. No outside theorem is inferred from a search snippet.

The whole proposal may be a routine or already known disk specialization of existing equality methods. A complete independent contribution review must compare that possibility explicitly. The present proof and its spectral multiplicity bound are unreviewed. No count changes, minimal-dimension claim or worldwide priority assertion is made.
