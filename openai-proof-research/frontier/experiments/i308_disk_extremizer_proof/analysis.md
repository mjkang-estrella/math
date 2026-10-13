# I308 — independent mathematical analysis

Verdict: **PASS unchanged**, for the complete authenticated I307 theorem/proof and its nilpotent/R019 consequence. All OpenAI theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. This analysis proves the new deductions rather than assuming the proposal's conclusion. No external equality theorem is a premise.

## 1. Scope, calculus, and the upper bound

Let A be a finite complex matrix with w(A)≤1 and ρ(A)<1. Let f be holomorphic on the open unit disk with |f|≤1. Its Taylor coefficients obey |f_k|≤1 by Cauchy's estimate on smaller circles and passage to radius one.

Choose ρ(A)<s<1. There is C_s<∞ with ||A^k||≤C_s s^k. To verify this without a norm assumption on A, use Jordan form: a block λI+J has powers ∑_(j=0)^(ν-1) binom(k,j)λ^(k-j)J^j, with nilpotent zero-eigenvalue blocks eventually zero. Polynomial factors in k are absorbed by s^k after first choosing a radius strictly between ρ(A) and s. Similarity changes only C_s. Thus ∑||A^k||<∞. The Taylor calculus ∑f_k A^k is absolutely norm convergent. The same reasoning applies to every bounded holomorphic h and to fg or gf for polynomial g. Their coefficient products can be rearranged absolutely, giving (fg)(A)=f(A)g(A) and (gf)(A)=g(A)f(A). No assertion ||A||≤1 is used.

The pinned `thm:main` actually states the constant-two inequality for every finite matrix-valued polynomial, with the base-first convention, on W(A). Since W(A)⊂closed disk, it implies ||p(A)||≤2||p||_disk for scalar polynomials, and the analogous complete estimate. This premise is independent of every equality deduction below. The analytic-domain theorem assumes W(A)⊂Ω; it is not directly applied with Ω the open unit disk when W(A) touches its boundary.

For completeness its scalar estimate extends to this open-disk f as follows. For 0<t<1, f_t(z)=f(tz) is analytic past the closed unit disk and disk bounded by one. Let T_(t,n) be its Taylor partial sums. They converge uniformly on the closed disk. Put d_(t,n)=max(1,||T_(t,n)||_disk). Then d_(t,n)→1, and T_(t,n)/d_(t,n) are disk-bounded polynomials converging uniformly to f_t. Their evaluations converge to f_t(A). One may see this from coefficient convergence and the preceding geometric power bound, or uniform convergence on a circle of radius between ρ(A) and one. Finally f_t(A)→f(A) by dominated convergence in ∑t^k f_k A^k. Therefore ||f(A)||≤2. This argument also gives polynomial/Schur supremum equality; for nilpotent A it uses only finitely many coefficients. It imports no desired equality classification.

## 2. Singular vectors and the unweighted diagonal bounds

Assume now ||f(A)||=2. Finite dimension supplies unit x with f(A)*f(A)x=4x. Set y=f(A)x/2; then ||y||=1 and f(A)*y=2x. Define

    m_k=y*A^k x, p_k=x*A^k x, q_k=y*A^k y, l_k=x*A^k y,
    a²=∑_(k≥0)|m_k|².

All sequences decay geometrically. Their generating functions are the compressions M,P,Q,L of R(z)=(I-zA)^(-1), analytic on a disk of radius greater than one. In particular p_0=q_0=1 and l_0=conjugate(m_0).

The scalar functional is bilinear in h_k and m_k:

    y*h(A)x=∑h_k m_k,    |∑h_k m_k|≤a(∑|h_k|²)^(1/2).

The representer in the usual complex Hilbert-space pairing is conjugate(m_k); replacing it by m_k would be an error. Absolute convergence was proved above.

For every g∈H² and every 0<t<1, radial Parseval gives

    ∑|(fg)_k|²t^(2k)=∫|f(te^(iθ))g(te^(iθ))|² dθ/(2π)
                         ≤∫|g(te^(iθ))|² dθ/(2π)
                         =∑|g_k|²t^(2k).

Monotone convergence as t increases to one proves ||fg||_(H²)≤||g||_(H²). This uses no boundary extension or pointwise boundary values of f. Taking g=1 also gives ∑|f_k|²≤1.

The singular pair and the multiplicative calculus give, for polynomial g,

    y*(fg)(A)x=2x*g(A)x,    y*(gf)(A)x=2y*g(A)y.

Apply the coefficient functional to these products and the multiplier bound to obtain |∑g_k p_k|≤(a/2)||g||_(H²), and the same for q. For the finite polynomial g_n(z)=∑_(k=0)^n conjugate(p_k)z^k, let s_n=∑_(k=0)^n|p_k|². The inequality says s_n≤(a/2)√s_n, so s_n≤a²/4. Pass to the limit and repeat with conjugate(q_k). This proves the genuinely unweighted inequalities

    ∑|p_k|²≤a²/4,    ∑|q_k|²≤a²/4.

The constant coefficients give a²≥4. In the source, finite Faber tests have weights 1,2,2,… and dual weights 1,1/2,1/2,… . Here exact Taylor Parseval produces weights all one. This improvement is derived, not asserted by specialization of the source's weaker bound.

## 3. Positive compression and every equality extraction

On |z|=1 put B=I-zA. It is invertible by ρ(A)<1. Since RB=I and B*R*=I,

    B*(R+R*)B=B*+B=2I-zA-conjugate(z)A*.

For any v, the last quadratic form is 2||v||²-2Re(z v*Av)≥0 by w(A)≤1. Thus H=R+R*≥0. This works at numerical-radius equality as well as strict inequality.

The compression by [x,y] is

    Δ=[[D_x,conjugate(C)],[C,D_y]],
    D_x=P+conjugate(P), D_y=Q+conjugate(Q), C=M+conjugate(L).

No independence of x,y is needed for positivity. The determinant condition gives |C|²≤D_xD_y; hence 2|C|²≤D_x²+D_y². Use normalized circle measure throughout. Distinct positive and negative Fourier frequencies give

    ∫D_x²=4+2∑_(k≥1)|p_k|²=2+2∑_(k≥0)|p_k|²≤2+a²/2,
    ∫D_y²≤2+a²/2,
    ∫|C|²=4|m_0|²+∑_(k≥1)(|m_k|²+|l_k|²)
           =a²+3|m_0|²+∑_(k≥1)|l_k|².

In the cross identity the constant is 2m_0, not m_0, since conjugate(l_0)=m_0. Consequently

    2a²≤2∫|C|²≤∫D_x²+∫D_y²≤4+a².

It follows that a²≤4. Combined with a²≥4 this gives a²=4. Each diagonal sum is at most one and already has constant contribution one; therefore p_k=q_k=0 for k≥1. All endpoints in the last chain now equal eight, so its first inequality is an equality. The nonnegative excess 3|m_0|²+∑_(k≥1)|l_k|² vanishes. Thus m_0=0, l_k=0 for k≥1, and also l_0=0. This proves all asserted constant and backward vanishings individually.

Now D_x=D_y=2 and C=M. Positivity yields |M(z)|≤2 on the circle. Parseval gives ∫|M|²=a²=4. Since M is continuous there, a nonnegative continuous deficit 4-|M|² with integral zero vanishes at every point. Thus |M|=2 everywhere on the circle. No almost-everywhere conclusion is substituted for the claimed pointwise one.

The source's boundary parameter w uses R_boundary(w)=(I-A/w)^(-1). Our analytic R(z) equals R_boundary(w) when z=w^(-1) on the circle. This reverses Fourier signs but does not conjugate coefficient m_k. The forward scalar evaluation pairs ∑f_k m_k, and its Hilbert-space representer conjugates m_k. These two operations must be kept distinct.

## 4. Recovering the entire open-disk function

The singular convention gives

    2=y*f(A)x=∑f_k m_k,
    2≤(∑|f_k|²)^(1/2)(∑|m_k|²)^(1/2)≤2.

Equality requires ||f||_(H²)=1 and f_k=c conjugate(m_k). Substituting into the **real positive** pairing 2=c a² fixes c=1/2, with no free unnoticed phase. Hence for every k≥0,

    f_k=conjugate(m_k)/2=x*(A*)^k y/2,
    f(z)=x*(I-zA*)^(-1)y/2=conjugate(M(conjugate(z)))/2.

This is an identity of all Taylor coefficients and thus of functions throughout the disk. It is not merely equality modulo the minimal polynomial. Since ρ(A*)<1, it extends holomorphically beyond the closed disk. The established boundary modulus of M gives |f|=1 on the circle. Also f(0)=0 and f is nonzero, since ||f(A)||=2. Rationality, innerness, boundary regularity, and a zero at zero have all been deduced, not assumed.

## 5. Factorization, denominator cancellation, and the zero-block bound

Let ℓ=deg μ_A and define ν_0=0 provisionally if zero is absent. The minimal polynomial of A* is μ_(A*)(t)=∏_(λ∈σ(A))(t-conjugate(λ))^(ν_λ). Its reversed polynomial is

    q(z)=z^ℓ μ_(A*)(1/z)=∏(1-conjugate(λ)z)^(ν_λ),
    q(0)=1, deg q=ℓ-ν_0.

The identity q(z)(I-zA*)^(-1)=T(z), with T a matrix polynomial of degree at most ℓ-1, follows directly by multiplying the power series: every coefficient of degree at least ℓ is zero by the minimal-polynomial recurrence. This retains the degree ℓ-1 bound even when zero eigenvalues lower deg q. Applying x*(·)y/2 gives f=p/q with deg p≤ℓ-1 and p≠0.

Because f is analytic in a neighborhood of the closed disk, nonzero, and has unit circle modulus, it has finitely many zeros inside and none on the circle. Divide by the finite Blaschke factors for all these zeros with multiplicities. The quotient and its reciprocal are holomorphic on the disk and continuous on its closure; both have circle modulus one. The maximum principle gives modulus identically one and hence a unimodular constant. Thus f is a finite Blaschke product. Its zero at zero has order r≥1.

Every nonzero zero α contributes the pole 1/conjugate(α). Numerator zeros of a Blaschke product lie inside the disk; denominator zeros lie outside it. Therefore these poles cannot cancel against any numerator zero, including zeros from other factors. They must be poles allowed by q. Matching 1/conjugate(α)=1/conjugate(λ) gives α=λ, with multiplicity at most ν_λ. This proves the support and exponent claims without an eigenvalue distinctness or genericity assumption.

Write K=∑_(λ≠0) k_λ. The reduced denominator d=∏_(λ≠0)(1-conjugate(λ)z)^(k_λ) has degree K and divides q. The reduced numerator has degree r+K: none of its leading factors has zero leading coefficient. Restoring q/d, of degree ℓ-ν_0-K, gives the original numerator p of degree exactly r+ℓ-ν_0. Multiplication of nonzero polynomials cannot lower this degree. Thus

    r+ℓ-ν_0≤ℓ-1, so r≤ν_0-1.

If zero is absent, ν_0=0 in this calculation and r≤-1, a contradiction. If its largest block has size one, r≤0, again a contradiction. Therefore zero is present with ν_0≥2 and 1≤r≤ν_0-1. These are necessary conditions only. The proof has not asserted every allowed Blaschke product attains two.

## 6. Nilpotent maxima, polynomial approximation, and strict gaps

Keep w(A)≤1 and suppose A has nilpotence index L, meaning A^L=0 and A^(L-1)≠0. Then σ(A)={0}, ν_0=L, and the proved classification gives f=ηz^r for 1≤r<L whenever ||f(A)||=2. Conversely if ||A^r||=2, z^r is a Schur polynomial attaining two. This establishes the attained-equality criterion first.

To pass to suprema, take any sequence of Schur functions f_j. Each coefficient is in the closed unit disk. A diagonal subsequence has coefficient limits c_k for every k. For any R<1, the geometric tail bound ∑_(k≥n)R^k→0, uniformly in j, shows ∑c_k z^k is the locally uniform limit. Therefore its modulus is ≤1 and it is a Schur function f. Since f_j(A)=∑_(k=0)^(L-1)(f_j)_k A^k, coefficient convergence gives norm convergence to f(A). The evaluation image of the Schur ball is compact in finite-dimensional matrix space. Its norm supremum is a maximum.

The upper bound in Section 1 gives this maximum at most two. If the supremum is two, a limiting Schur function attains two and hence a power attains two. Conversely a power equality gives supremum two. If every relevant power has norm strictly below two, the maximum is strictly below two. This is a positive gap for each fixed A, with no computed uniform gap over matrices.

Every disk-bounded polynomial is Schur. Conversely for every Schur h, dilation h(tz), its uniformly convergent Taylor polynomials, and normalization by max(1,disk norm) approximate its evaluation, as in Section 1. For nilpotent A evaluation depends on L coefficients; the dilation limit is immediately finite and continuous. Thus polynomial and Schur suprema agree. Normalizing by max(1,disk norm) also covers zero polynomials and disk norms below one without changing the limit. There is no inference from separate nonattainment of every polynomial to a gap.

When L=1, A=0. Then ||f(A)||=|f(0)|≤1, and the supremum is one. The existential condition 1≤r<L is empty and false. This matches the criterion and is not an exception to it.

## 7. Independent check of the R019 consequence

Use the exact N and P specified in R019. Assign heights (3,2,1,2,1,0). The nonzero N entries raise height by one, so N⁴=0. Direct multiplication gives

    N²e3=(3/2)e1, N²e5=(√14/4)e1, N²e6=(5√2/4)e4,
    N³=(√7/2)e1e6*,

with the other N² columns zero. Thus the index is four.

For N, the blocks of successive height spaces have the two outer squared norms 2, and middle block

    K=[[8/5,0],[-3√14/20,5/4]],
    K*K=[[23/8,-3√14/16],[-3√14/16,25/16]].

Its trace is 71/16 and eigenvalue difference is 3√105/16, giving eigenvalues (71±3√105)/32. The larger exceeds 2 and is below 4 since √105<19. For N² the two nonzero orthogonal height blocks are the row (3/2,√14/4) and the column (0,5√2/4), both squared norm 25/8. The rank-one N³ has squared norm 7/4. This independently verifies exactly the existing I287 Section 10 values, with no floating-point calculation or parameter scan.

The accepted W(N)=closed disk can also be checked directly from the displayed data used here. Height conjugation rotates N. In the bipartite coordinate order, Re N has off-diagonal block C from R019 and CC*=I-aa* with a=(√2/2,-3√2/8,-√7/8). Multiplication yields diagonal entries (1/2,23/32,57/64), cross entries (3/8,√14/16,-3√14/64), and ||a||²=57/64. Thus C has singular values 1,1,√7/8 and every support function is one. In particular w(N)=1, as required for the generic theorem.

For the complete lower bound, P is unitary on the circle since its columns have squared norm (9+7)/16 and their inner product is zero. Scalar matrix-element maximum principles give ||P||_disk=1. Let ell=(√7/5)e2-(3√2/5)e4 and x=(e3⊗f1+e6⊗f2)/√2, y=(e1⊗f1+ell⊗f2)/√2. Their norms are one. The displayed powers give the first coefficient component of P[N]x as (9/8+7/8)e1/√2=2e1/√2 and the second as (2√7 e2/5-6√2 e4/5)/√2=2ell/√2. Hence P[N]x=2y. The stipulated complete polynomial bound supplies ||P[N]||≤2 and the complete supremum ≤2. This checks exactly the attainment needed here without reauditing unrelated irreducibility or Schmidt-channel conclusions.

No power with 1≤r<4 has norm two. Section 6 gives C_scalar(N)<2, and the last paragraph gives C_complete(N)=2. This proves the complete claimed G306 consequence through I307. The older ACV-dependent route in I306 is not needed or imported; neither is I287's optional polynomial-only rigidity theorem. No separate new finding is nominated.

## 8. Repairs and limits

No genuine repair was needed. The spectral-radius estimate, finite dual tests, complete equality chain, reflected conjugation formula, reversed minimal polynomial, normalization choice, and coefficient compactness above expand compressed steps already present in I307. They do not change its assumptions or conclusion. The proof verdict does not certify contribution novelty, a reducing-block reformulation, or a quantitative gap. No equality classification is borrowed from the pinned upper-bound theorem. No unpaid mathematical operation remains for the exact assigned target.
