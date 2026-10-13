# I310 — a dimension-independent quantitative nilpotent scalar gap

2026-10-13. **Parent proof proposal, no independent gate passed.** This is a quantitative extension of the I307/I306 package. It is not a separate acceptance slot from that package. The qualitative I308 proof review is live and is not presumed to cover this additional estimate.

## Proposed theorem

Let L≥2 and let A be any finite complex matrix with A^L=0 and w(A)≤1. Put

    δ=2-max{1,||A||,||A²||,...,||A^(L-1)||},
    K_L=1+17·6^(L-1),
    D_L=1+2 sqrt(L) K_L.

The stipulated scalar disk bound applied to monomials gives δ∈[0,1]. For every Schur function f on the open disk, the proposed explicit estimate is

    ||f(A)|| ≤ 2 - (1/4)(δ/D_L)^(2^L).          (Q310)

The constant depends on the nilpotence bound L and power gap δ, not the base dimension, coefficients, boundary continuity or degree of f. The exponent and constants are not claimed optimal. This gives a uniform quantitative form of I307's strict alternative and applies to R019's matrix at L=4 with its strictly positive computed power gap.

## 1. Near-equality estimates from the scalar Hardy argument

Write γ=||f(A)||. Only γ≥sqrt(3) needs work. Let ε=4-γ²∈[0,1]. Choose singular unit vectors x,y and use I307's definitions of R,P,Q,M,L_0 and a²; write L_0 for its backward resolvent scalar to avoid conflict with the nilpotence bound. The proof below re-establishes the needed quantitative inequalities and does not assume that an exact-equality statement has a quantitative version.

The same ordered tests give

    Σ|p_k|², Σ|q_k|² ≤ a²/γ²,
    a² ≥ γ².

The latter follows by Cauchy–Schwarz in γ=Σ f_k m_k and ||f||_H²≤1. The positive two-by-two boundary compression and Parseval give

    2a² ≤ 4+4a²/γ²,
    a² ≤ 2γ²/(γ²-2) ≤ 6.

Consequently Σ_(k≥1)|p_k|² and Σ_(k≥1)|q_k|² are at most ε. For the real diagonal fields D_x=P+conjugate(P), D_y=Q+conjugate(Q),

    ||D_x-2||_2, ||D_y-2||_2 ≤ sqrt(2ε).

Let C=M+conjugate(L_0). Exact Parseval reads

    ||C||_2²=a²+b,
    b=3|m_0|²+Σ_(k≥1)|l_k|².

Since 2(a²+b)≤4+4a²/γ² and the coefficient 2/γ²-1 is negative,

    0≤b≤2+a²(2/γ²-1)≤4-γ²=ε.

In particular ||L_0||_2≤sqrt(ε). Positivity also gives 0≤D_xD_y-|C|² pointwise. Its integral is at most (4+2ε)-(4-ε)=3ε. Further,

    ||D_xD_y-4||_1 ≤4sqrt(2ε)+2ε.

Thus |||C|²-4||_1≤4sqrt(2ε)+5ε. Replacing C by M costs at most

    || |C|²-|M|² ||_1
       ≤||L_0||_2(2||M||_2+||L_0||_2)
       ≤2sqrt(6ε)+ε.

For the polynomial q(z)=Σ conjugate(m_k)z^k/2, of degree at most L-1, we have therefore

    ||q||_2≤sqrt(3/2)<2,
    η:=|||q|²-1||_1 ≤(17/4)sqrt(ε).             (1)

All circle norms use normalized Haar measure. The numerical constant 17 follows from 4sqrt(2)+2sqrt(6)+6<17.

Finally the exact pairing gives

    ||f-q||_2²=||f||_2²+a²/4-γ
       ≤1+γ²/[2(γ²-2)]-γ
       =ε/[2(2-ε)]+ε/(2+γ) ≤ ε.              (2)

The equality case γ=2 is included by setting ε=0. No division by ε occurs.

## 2. Elementary stability of finite polynomial innerness

Claim: if a polynomial q has degree at most d, ||q||_2≤2, and η=|||q|²-1||_1, there are j∈{0,...,d} and |ζ|=1 with

    ||q-ζz^j||_2 ≤ C_d η^(1/2^d),
    C_d=(16·6^d-1)/5 ≤4·6^d.                  (3)

For d=0, ||q|-1|≤η, and the larger constant C_0=3 is valid. If η≥1, the trivial distance bound ||q||_2+1≤3 proves (3) in every degree. Suppose 0<η<1 and d≥1. The d-th Fourier coefficient of |q|²-1 is c_d conjugate(c_0); hence |c_0c_d|≤η. At least one endpoint coefficient has modulus at most sqrt(η). Delete that coefficient, dividing by z if the deleted endpoint is c_0. This yields a polynomial q_1 of degree at most d-1, with ||q_1||_2≤2 and an H² error sqrt(η), up to the corresponding monomial shift. Its flatness error is at most

    η_1≤η+2||q||_2 sqrt(η)+η≤6sqrt(η).

Apply the inductive assertion, whether η_1 is below or above one. Since sqrt(η)≤η^(1/2^d), the resulting constant is at most 1+6 C_(d-1). This is exactly C_d above. The same argument at η=0 deletes a zero endpoint coefficient without error and proves the exact monomial assertion. This proves the claim, including polynomials whose actual degree is smaller than d.

## 3. Return to the matrix

Apply (3) with d=L-1 and (1), and then use (2). Since ε≤1 and (17/4)^(1/2^(L-1))≤17/4,

    ||f-ζz^j||_H² ≤ K_L ε^(1/2^L)

for some 0≤j<L. Evaluation at A uses only the first L coefficients. Each ||A^k|| is at most two (including the sharper ||I||=1), so coefficient Cauchy–Schwarz gives

    ||f(A)-ζA^j|| ≤ 2sqrt(L) K_L ε^(1/2^L).

By definition ||A^j||≤2-δ even for j=0. Therefore

    δ≤(2-γ)+2sqrt(L)K_L ε^(1/2^L)
      ≤D_L ε^(1/2^L).

It follows that ε≥(δ/D_L)^(2^L). Since 2-γ=ε/(2+γ)≥ε/4, this is (Q310). If γ<sqrt(3), the same conclusion is automatic: its proposed right-hand side is at least 7/4>sqrt(3), because δ≤1 and D_L≥1. This covers every f and proves the proposed uniform estimate.

## Status and scope

The proof uses the original scalar disk resolvent argument underlying I307, the stipulated upper bound for powers, and an explicit polynomial endpoint-deletion induction. It does not invoke a qualitative compactness argument to obtain its constant. The finite-dimensional bound L controls only the number of Taylor coefficients needed; the base dimension may be arbitrarily large.

No independent reviewer has yet checked these inequalities, the constants, the polynomial lemma, or the claimed uniformity. The coefficient exponent is deliberately weak; it is not called sharp. The contribution comparison must include old nilpotent functional-calculus bounds, quantitative polynomial innerness and existing equality stability. This quantitative strengthening belongs to the same pending scalar/complete-gap package, and does not add another accepted finding.
