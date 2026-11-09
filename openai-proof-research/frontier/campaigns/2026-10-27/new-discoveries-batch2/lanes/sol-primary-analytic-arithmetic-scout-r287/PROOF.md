# Full ordinary refutation of Csordas–Forgács Problem 37

Scientific status: full ordinary endpoint, separately checked exact rational certificate. Novelty/substantiveness HOLD; no acceptance, Lean, manuscript or count claimed.

Source: G. Csordas and T. Forgács, *Multiplier sequences, classes of generalized Bessel functions and open problems*, arXiv:1505.00355v1, 2 May 2015, Definition 4 p2 and Problem 37 p16. The separately retrieved v2 retains the same question on p16. For every real polynomial p, a CZDS must satisfy Z_C(Tp)≤Z_C(p), counting multiplicities, with T(x^k)=γ_k x^k. Here γ_k=(k²+k+1)/k!, strictly positive for every k≥0. No restriction to real-rooted p appears in Definition 4.

## Route A: exact finite witness giving the full endpoint

Put λ_k=k!/(k²+k+1). Define the rational symmetric 37×37 matrix

    A_ij = λ_(i+j)/(i!j!),       0≤i,j≤36.

The following recurrences specify rational numbers uniquely, without numerical tolerances. Set L_jj=1, L_ij=0 for i<j. In ascending order j=0,…,36 set

    d_j = A_jj − Σ_(k<j) L_jk² d_k,
    L_ij = (A_ij − Σ_(k<j) L_ik L_jk d_k)/d_j   (i>j).

Exact calculation gives d_j>0 for 0≤j≤35 and d_36<0. The hexadecimal numerator/denominator certificate in moment-witness.json is an exact rational representation, not a floating approximation. Hexadecimal avoids Python's decimal serialization limit without raising that limit. The recurrences and all first 37 pivot signs are in hankel.py and hankel-checks.json.

Let v solve Lᵀv=e_36 and put r(x)=Σ_(i=0)^36 v_i x^i/i!. Thus v_36=1, r has degree36, and by A=LDLᵀ,

    Λ(r²) = Σ_(i,j) (v_i/i!)(v_j/j!) λ_(i+j)
          = vᵀAv = d_36 < 0,

where Λ(x^k)=λ_k. Set ε=−d_36/2>0, g=r²+ε, and define f coefficientwise by f_k=λ_k g_k. These are rational real polynomials of degree72. Since λ_0=1,

    f(1)=Λ(r²)+ε=d_36/2<0.

The leading coefficient of f is λ_72/(36!)²>0. Hence f(x)→+∞ as x→±∞. The intermediate value theorem gives one real root in (−∞,1) and another in (1,∞). In particular Z_C(f)≤70. On the other hand, for every real x, g(x)=r(x)²+ε>0, so Z_C(g)=72. Finally T(f)=g, since γ_k λ_k=1 for every k. Consequently

    Z_C(Tf)=72>70≥Z_C(f).

This disproves the literal universal source endpoint. No exact count of the remaining roots of f is needed. No claim that the input has only two real roots is made. The verifier independently recomputes the direct quadratic functional, convolution square, diagonal identity, sign at1, and leading sign from the certificate; it does not regenerate LDL or use numerical roots. witness-verification.json records PASS and the witness hash.

## Route B: analytic explanation independent of the finite pivot search

This second route explains why the obstruction is structural. It is not required to trust Route A's exact certificate.

Write a=√3/2. On (0,∞) define the signed integrable density

    w(t)=a^(−1) ∫_0^1 u^(−3/2) sin(a log(1/u)) exp(−t/u) du.

Absolute Fubini is valid for every nonnegative integer moment: replacing sin by1 and integrating t^k first bounds the absolute integral by k!/[a(k+1/2)]. Direct evaluation then gives

    ∫_0^∞ t^k w(t)dt
       = (k!/a) ∫_0^1 u^(k−1/2) sin(a log(1/u))du
       = k!/[(k+1/2)²+a²] = λ_k.

For every 0<c<1, the same argument bounds ∫exp(ct)|w(t)|dt by a^(−1)∫_0^1 u^(−1/2)/(1−cu)du<∞. After y=t/u,

    w(t)=t^(−1/2)/a · Im[t^(−ia) ∫_t^∞ y^(−1/2+ia) exp(−y)dy].

The integral is Γ(1/2+ia)+O(√t), with error at most2√t. Gamma has no zeros. Therefore w(t) is a nonzero sinusoid in log(1/t), multiplied by t^(−1/2), plus a bounded error. On a sequence tending to0 its sinusoidal factor is −|Γ(1/2+ia)|; w is negative there and by continuity on nonempty intervals.

Suppose T were CZDS. For every strictly positive real polynomial h of even degree, f=T^(−1)h has the same degree and positive leading coefficient. Since h has no real roots, CZDS would force f to have no real roots, whence f>0 on R. Applying this to h=s²+δ and taking δ↓0 yields Λ(s²)≥0 for every real polynomial s. The Hamburger moment theorem gives a positive measure μ with moments λ_k. This is exactly the necessary moment-functional bridge exhibited in Craven–Csordas, *Methods Appl. Anal.*2(4)(1995), Theorem1.7 and discussion p423; its primary body is frozen here.

This μ has exponential moments: for c<1, monotone convergence gives ∫cosh(cx)dμ=Σ c^(2k)λ_(2k)/(2k)!≤Σ c^(2k)<∞. Since exp(c|x|)≤2cosh(cx), its Fourier transform is analytic in a strip. The signed measure w(t)dt has the same property, and the same moments. Their analytic Fourier transforms agree near0 by their convergent Taylor series, hence throughout the connected strip. Uniqueness of Fourier transforms of finite signed measures gives μ=w(t)dt. This is impossible because w is negative on an interval. Thus T is not CZDS.

## Classical bridges and the strongest objection

Craven–Csordas1995 Example1.8 p423 already refutes {k²+k+1}, using both a reciprocal moment determinant and a polynomial witness. This is a genuine closest prior proof body, not merely a title match. It does NOT refute {(k²+k+1)/k!}: composition with the known CZDS {1/k!} can destroy the old witness. Indeed the structured search here found no increase in15,000 numerical tests. Their Theorem2.13 classifies polynomial interpolants, whereas our sequence is not a polynomial in k. Applying that theorem to k²+k+1 and then cancelling a factorial diagonal is invalid: the inverse factorial map is not supplied as a CZDS.

The exact bridge that DOES work is their necessary reciprocal-moment criterion, followed by the new displayed rational λ-matrix obstruction and the inverse-square witness. Thus the technique is classical; the full exact source instance and its prior publication status need independent assessment. No discovery credit is inferred from a large determinant, generic tools, or apparent proof length. The source2015 itself raises this factorial-modified endpoint after citing the1995 classification; a routine-subsumption objection must explain how that older full theorem already yields this exact factorial endpoint. The analytic inversion above is an explicit bridge a reviewer should assess, not an assertion of worldwide novelty.
