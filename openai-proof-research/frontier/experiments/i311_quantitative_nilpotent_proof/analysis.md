# I311 — independent quantitative proof analysis

Verdict: **PASS unchanged** for the entire authenticated I310 proposal, including the exact constants and all boundary cases. OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. The following deductions are independent of the finalized qualitative I308 verdict.

## 1. Functional calculus and the only stipulated upper bound

Let L≥2 be an integer, A a finite complex matrix, A^L=0, and w(A)≤1. Thus W(A) lies in the closed unit disk. The actual pinned `thm:main` with scalar coefficients gives ||p(A)||≤2 max_(|z|≤1)|p(z)|. Applying it to z^k gives ||A^k||≤2 for every k≥1; ||A^0||=1. Consequently δ=2-max_(0≤k<L)||A^k|| lies in [0,1]. These power norms are bounded independently of the base dimension.

For a scalar Schur function f(z)=∑f_k z^k on the open disk, set f(A)=∑_(k=0)^(L-1) f_k A^k. Evaluation of any analytic function uses this finite jet. Coefficient convolution gives (fg)(A)=f(A)g(A) and (gf)(A)=g(A)f(A) for polynomial g. No hypothesis ||A||<1 is needed.

To justify γ=||f(A)||≤2 using precisely the pinned polynomial theorem, fix 0<t<1. Taylor polynomials T_n of f(tz) converge uniformly on the closed disk. Dividing T_n by max(1,||T_n||_disk) gives disk-bounded polynomials with normalization tending to one. Their first L coefficients converge to those of f(tz), so the pinned bound gives ||f(tA)||≤2. Let t increase to one in the finite coefficient evaluation. This proves γ≤2. It uses neither boundary continuity of f nor an equality classification. The source's `thm:domain` requires W(A)⊂Ω and is not directly invoked for Ω the open unit disk when w(A)=1.

For any g∈H², radial Parseval gives

    ∑|(fg)_k|²r^(2k)=∫|f(re^(iθ))g(re^(iθ))|²dθ/(2π)
                    ≤∑|g_k|²r^(2k), 0<r<1.

Monotone convergence gives ||fg||_(H²)≤||g||_(H²). In particular ||f||_(H²)≤1. Circle norms of the resolvent polynomials below use normalized Haar measure; H² norms of f are coefficient norms, so no initial boundary values of f are required.

## 2. Ordered coefficient tests and positive blocks

It suffices first to consider γ≥sqrt(3). Put ε=4-γ²∈[0,1]. A top singular pair supplies unit x,y with f(A)x=γy and f(A)*y=γx; γ is real and positive. Define

    R(z)=(I-zA)^(-1)=∑_(k=0)^(L-1)z^k A^k,
    P=x*Rx, Q=y*Ry, M=y*Rx, B=x*Ry,
    p_k=x*A^k x, q_k=y*A^k y, m_k=y*A^k x, l_k=x*A^k y,
    a²=∑|m_k|².

Here B denotes the whole backward scalar function called L_0 in Q310. All moments vanish for k≥L. We have p_0=q_0=1 and l_0=conjugate(m_0). For every analytic h, y*h(A)x=∑h_k m_k, a bilinear coefficient pairing. The conjugate representer is conjugate(m_k), not m_k.

For a polynomial g, the singular relations and evaluation multiplication give

    γx*g(A)x=y*(fg)(A)x,
    γy*g(A)y=y*(gf)(A)x.

The coefficient pairing followed by the H² multiplier contraction bounds each diagonal functional by (a/γ)||g||_(H²). Test with g=∑_(k=0)^(L-1)conjugate(p_k)z^k. Its paired value and squared norm both equal ∑|p_k|², hence ∑|p_k|²≤a²/γ². The same test with conjugate(q_k) gives ∑|q_k|²≤a²/γ². The forward pairing γ=∑f_k m_k and ||f||_(H²)≤1 give a²≥γ². These unweighted bounds are re-derived; the source's weighted Faber bound is not silently strengthened.

On |z|=1 the invertible matrix T=I-zA satisfies

    T*(R+R*)T=T*+T=2I-zA-conjugate(z)A*≥0.

Indeed Re(z v*Av)≤||v||² by numerical radius. Thus the original R+R* is positive even when w(A)=1. Compression by [x,y], which need not have independent columns, gives

    Δ=[[D_x,conjugate(C)],[C,D_y]]≥0,
    D_x=P+conjugate(P), D_y=Q+conjugate(Q), C=M+conjugate(B).

Therefore |C|²≤D_xD_y and 2|C|²≤D_x²+D_y² pointwise. Exact Parseval gives

    ∫D_x²=4+2∑_(k≥1)|p_k|²=2+2∑|p_k|²≤2+2a²/γ²,
    ∫D_y²≤2+2a²/γ²,
    ∫|C|²=4|m_0|²+∑_(k≥1)(|m_k|²+|l_k|²)=a²+b,
    b=3|m_0|²+∑_(k≥1)|l_k|²≥0.

The cross constant is 2m_0 since conjugate(l_0)=m_0. Combining the bounds yields

    2(a²+b)≤4+4a²/γ²,
    γ²≤a²≤2γ²/(γ²-2)≤6.

The denominator γ²-2≥1 is positive. The last inequality follows from 2s/(s-2)≤6 for s≥3, equivalently s≥3.

The diagonal nonconstant moments satisfy

    ∑_(k≥1)|p_k|²≤a²/γ²-1≤2/(γ²-2)-1
                          =ε/(2-ε)≤ε,

and similarly for q_k. Hence with u=D_x-2 and v=D_y-2, both mean zero, ||u||_2,||v||_2≤sqrt(2ε).

For the backward budget the important coefficient is negative:

    b≤2+a²(2/γ²-1)≤2+γ²(2/γ²-1)=4-γ²=ε.

The second inequality uses the LOWER bound a²≥γ² and reverses its effect on multiplication by 2/γ²-1<0. No upper bound is substituted into this negative expression. Also

    ||B||²_2=|m_0|²+∑_(k≥1)|l_k|²≤b≤ε.

## 3. L¹ flatness and exact H² approximation

Let S=D_xD_y-|C|²≥0. Since ∫D_xD_y=4+∫uv≤4+2ε, whereas ∫|C|²=a²+b≥γ²=4-ε, one obtains 0≤∫S≤3ε. The product expansion gives

    ||D_xD_y-4||_1=||2u+2v+uv||_1
                   ≤2||u||_2+2||v||_2+||u||_2||v||_2
                   ≤4sqrt(2ε)+2ε.

Thus |||C|²-4||_1≤4sqrt(2ε)+5ε. Since C=M+conjugate(B),

    |||C|²-|M|²||_1≤2||M||_2||B||_2+||B||²_2
                   ≤2sqrt(6ε)+ε.

Define q(z)=∑conjugate(m_k)z^k/2=conjugate(M(conjugate(z)))/2. Conjugation alone at the same z would not give this analytic polynomial. Reflection z↦conjugate(z) preserves Haar measure, so

    ||q||_2=a/2≤sqrt(3/2)<2,
    η=|||q|²-1||_1=(1/4)|||M|²-4||_1
      ≤(1/4)(4sqrt(2ε)+2sqrt(6ε)+6ε)
      ≤(17/4)sqrt(ε).

The final step uses ε≤sqrt(ε) for 0≤ε≤1 and 4sqrt(2)+2sqrt(6)+6<17. An exact elementary certificate is sqrt(2)<3/2 and sqrt(6)<5/2, so the sum is strictly less than 6+5+6=17. There is no numerical scan.

The singular-pair phase makes the pairing ∑f_k m_k=γ real positive. Writing q̂_k=conjugate(m_k)/2 for the polynomial coefficients (distinct from the diagonal moments q_k), we have ∑f_k conjugate(q̂_k)=γ/2. The entire H² coefficient norm, including f's tail, therefore obeys the exact identity

    ||f-q||²_2=||f||²_2+a²/4-γ
              ≤1+γ²/[2(γ²-2)]-γ
              =ε/[2(2-ε)]+ε/(2+γ)≤ε.

To check the displayed algebra, γ²=4-ε gives γ²/[2(γ²-2)]=1+ε/[2(2-ε)], and 2-γ=ε/(2+γ). For the final inequality, 1/[2(2-ε)]≤1/2 and 1/(2+γ)≤1/(2+sqrt(3))<1/2. This proof works directly at ε=0 without division by ε.

## 4. Polynomial endpoint-deletion stability

We prove the exact lemma in Q310 for every integer d≥0: for degree at most d, H² norm at most 2, and η=|||q|²-1||_1, a unimodular monomial ζz^j with 0≤j≤d has H² distance at most C_d η^(1/2^d), where C_d=(16·6^d-1)/5.

For d=0 put a=|c_0|. If c_0≠0 take ζ=c_0/a; if c_0=0 take any unimodular ζ. Then the distance is |a-1|=|a²-1|/(a+1)≤η. Thus C_0=3 is valid, including q=0. In any degree when η≥1, choose j=0 and any ζ; the triangle bound is at most ||q||_2+1≤3≤C_d η^(1/2^d).

For 0<η<1 and d≥1, pad coefficients through c_d. The coefficient of z^d in |q|²-1 is exactly c_d conjugate(c_0). Its absolute value is at most the L¹ norm η. Hence at least one endpoint has modulus ≤sqrt(η). This remains true when the actual degree is less than d, since c_d=0.

If |c_d| is small, set p=q-c_d z^d and q_1=p. Then deg q_1≤d-1 and ||q-q_1||_2≤sqrt(η). If |c_0| is small, set p=q-c_0 and q_1=p/z. The polynomial p has zero constant, so division by z is legal; now deg q_1≤d-1 and ||q-zq_1||_2≤sqrt(η). Deletion removes one orthogonal coefficient, and multiplication or division by z preserves H² norm on the relevant subspace. Thus ||q_1||_2≤||q||_2≤2 in both cases; shifts change neither circle modulus nor flatness.

Writing r for the deleted monomial, with ||r||_2≤sqrt(η), gives

    η_1=|||q_1|²-1||_1=|||q-r|²-1||_1
        ≤η+2||q||_2||r||_2+||r||²_2
        ≤2η+4sqrt(η)≤6sqrt(η).

The induction hypothesis applies to this q_1 whether η_1 is zero, below one, or at least one. Lift its chosen monomial with no shift or with one z factor according to the deletion. Its exponent remains between zero and d. Let α=1/2^(d-1). Then

    distance≤sqrt(η)+C_(d-1)η_1^α
            ≤sqrt(η)+6^α C_(d-1)η^(1/2^d)
            ≤(1+6 C_(d-1))η^(1/2^d).

Here α≤1 implies 6^α≤6, and 0<η<1 with d≥1 implies sqrt(η)≤η^(1/2^d). These steps also cover η_1≥1 without any additional smallness assumption.

If η=0, the highest autocorrelation vanishes, so one endpoint is exactly zero. Delete it and make the same allowed shift with zero error. Flatness remains zero and the degree drops. Induction ends at a constant of modulus one. Thus distance zero is justified without taking a limit or dividing by η.

The recurrence C_0=3 and C_d=1+6C_(d-1) solves to (16·6^d-1)/5. Indeed substitution gives 1+6(16·6^(d-1)-1)/5=(16·6^d-1)/5. Finally C_d≤4·6^d follows from 16·6^d-1≤20·6^d. No stronger conclusion, boundary assumption, or generic coefficient hypothesis was inserted.

## 5. Dyadic exponent and first-L-coefficient evaluation

Apply the lemma with d=L-1. Then 1/2^d acts on η≤(17/4)sqrt(ε), giving ε exponent 1/2^(d+1)=1/2^L. For ε∈[0,1],

    ||f-ζz^j||_(H²)≤||f-q||_2+||q-ζz^j||_2
      ≤sqrt(ε)+4·6^d (17/4)^(1/2^d) ε^(1/2^L)
      ≤(1+17·6^(L-1))ε^(1/2^L)=K_L ε^(1/2^L).

We used sqrt(ε)≤ε^(1/2^L) and (17/4)^(1/2^d)≤17/4, also valid at ε=0 by the already established exact lemma. The exponent j satisfies 0≤j<L.

Write h=f-ζz^j. Since A^L=0, only its first L coefficients evaluate. The monomial power bound gives

    ||h(A)||≤∑_(k=0)^(L-1)|h_k| ||A^k||
             ≤(∑_(k=0)^(L-1)||A^k||²)^(1/2)
                (∑_(k=0)^(L-1)|h_k|²)^(1/2)
             ≤2sqrt(L)||h||_(H²).

In fact the first factor is at most sqrt(4L-3), but the stated constant 2sqrt(L) is valid unchanged. The full H² distance controls every first-L jet without dependence on the tail or its complexity.

Since ||A^j||≤2-δ, also for j=0 because ||I||=1 and δ≤1,

    γ≤2-δ+2sqrt(L)K_L ε^(1/2^L),
    δ≤(2-γ)+2sqrt(L)K_L ε^(1/2^L)
       ≤(1+2sqrt(L)K_L)ε^(1/2^L)=D_L ε^(1/2^L).

For the last inequality, 2-γ=ε/(2+γ)≤ε≤ε^(1/2^L); it also holds at ε=0. Since D_L>0, monotonicity of the nonnegative power gives ε≥(δ/D_L)^(2^L). The opposite comparison 2-γ=ε/(2+γ)≥ε/4 uses γ≤2, yielding exactly

    ||f(A)||=γ≤2-(δ/D_L)^(2^L)/4.

## 6. Boundary cases, verdict, and contribution limits

If γ<sqrt(3), δ≤1 and D_L≥1 make the proposed right-hand side at least 2-1/4=7/4. Since (7/4)²=49/16>3, γ<sqrt(3)<7/4 proves the result. This includes γ=0, so no singular-pair construction is needed there. The boundary γ=sqrt(3) belongs to the checked near-equality branch.

If δ=0 the asserted bound is simply γ≤2, already justified. If ε=0 in the near-equality branch, the derived estimate forces δ≤0, hence δ=0; the approximation identities give an exact monomial, and the stated bound holds with zero gap. There is no division by δ or ε. L may exceed the actual nilpotence index: all coefficient arrays can be padded with zeros and every step still uses degree at most L-1. A=0 is included (δ=1 and γ≤1). The j=0 outcome is permitted by the stability lemma and explicitly included in the norm maximum.

No necessary repair or unpaid operation remains. Expanding the dual tests, product-slack estimate, reflected conjugation, recurrence factor, and low-norm case explains compressed valid steps rather than replacing false ones. The exact exponent and all constants remain unchanged.

This is a proof verdict for the quantitative part of I307/I306. The authorized finalized I308 records establish background qualitative evidence but do not certify the quantitative calculations. R019 is unnecessary for the general theorem; its application is conditional only on its already supplied positive power gap. No I309 content was read. No contribution, acceptance, independent finding count, optimality, or priority verdict is made. No external equality/stability theorem, compactness extraction, numerical scan, subagent, git operation, publication, or shared-index mutation is used.
