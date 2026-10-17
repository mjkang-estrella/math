# O217: zero-field SK fluctuation universality with only a fourth-moment bound

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. This is an author proof submitted for independent proof and contribution review, not an independent verdict. The complete frozen target is `original-scope.md`; no quantifier has changed. Source theorems at openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## 1. Statement and notation

Fix β>0 and K≥1. For n≥2 set E={ {i,j}:1≤i<j≤n }, m=|E| and q=β/√n. For x∈R^E put

    F(x)=log Σ_(σ∈{−1,1}^n) exp[q Σ_(e={i,j}) x_e σ_iσ_j].

Let J_e be independent, mean zero and variance one, with E|J_e|⁴≤K. They need not have a common distribution. Let g_e be independent standard normals, and write c_G=EF(g), V=Var F(g). We prove, uniformly in n and all such coordinate laws,

    |EF(J)−c_G| ≤ C,                                      (1)
    |Var F(J)−V| ≤ C(1+√V),                               (2)

where C depends only on β,K. If a≥1, c∈R, and φ∈C⁶(R) has bounded derivatives of orders 0 through 6, then

    |Eφ((F(J)−c)/a)−Eφ((F(g)−c)/a)|
       ≤ C a⁻¹ Σ_(r=1)^6 ||φ^(r)||∞.                     (3)

At every fixed β>1, the stipulated Gaussian source supplies

    V/n^(1/3) → a₂(β)>0,
    (F(g)−c_G)/√V ⇒ ν_β.                                (4)

Consequently (1)–(3) imply, for every independent triangular array with one uniform fourth-moment bound,

    Var F(J)/n^(1/3) → a₂(β),
    (F(J)−EF(J))/sqrt(Var F(J)) ⇒ ν_β.                    (5)

The denominator in (5) is positive eventually, which is enough for the full-sequence asymptotic assertion. In particular no invalid finite-n claim for Rademacher disorder at n=2 is needed. There is no external field. No identical-distribution, symmetry, third-moment matching, fifth/sixth moment, or higher-moment convergence assumption/conclusion is inserted.

## 2. Uniform derivative and gauge facts

For an ordered list of k edges, possibly repeated, write D_𝐞 for the corresponding mixed partial derivative. For every k≥1 there is a finite number B_k, depending only on k, such that

    |D_𝐞 F(x)| ≤ B_k q^k    for all x.                   (6)

Indeed, under the finite Gibbs law at x, D_𝐞 F is q^k times the joint cumulant of the k variables s_e(σ)=σ_iσ_j. Each variable has absolute value one. The exact cumulant formula is

    κ(s_1,…,s_k)=Σ_(π partition of {1,…,k})
                (|π|−1)! (−1)^(|π|−1) ∏_(A∈π) E∏_(r∈A)s_r.

Thus one can take B_k=Σ_π (|π|−1)!. This proof applies without distinctness of the edge indices and without any assumption on x. In particular |∂_eF|≤q, so F is coordinatewise q-Lipschitz. Also

    |F(x)|≤ n log 2+q Σ_e |x_e|.                        (7)

For the test observable U(x)=φ((F(x)−c)/a), the multivariate chain rule gives, for 1≤k≤6,

    |D_𝐞 U(x)| ≤ C_k q^k a⁻¹ A_φ,
    A_φ=Σ_(r=1)^6 ||φ^(r)||∞,                            (8)

because a partition with r blocks contributes a^(-r)φ^(r) times a product of derivatives of F of total order k, and a^(-r)≤a⁻¹. The constant is independent of a,c,φ,n,x. For U=F, the same notation applies with a⁻¹A_φ replaced by 1. Write this common factor as L.

Fix a vertex i, and let T_i negate all incident coordinates. The bijection on spins that negates only σ_i proves the exact identity

    F(T_i x)=F(x).                                       (9)

This is an identity of deterministic functions, not a symmetry assumption on the disorder distribution. Every observable of the form Ψ(F) inherits (9). For an incident edge e={i,j}, differentiate (9) three times in x_e and then put x_e=0. If S is the other incident edges, |S|=n−2, and

    h(x_(E\{e}))=∂_e³U(x)|_(x_e=0),

then

    h(−x_S,x_(E\(S∪{e})))=−h(x_S,x_(E\(S∪{e}))).        (10)

The sign follows from three differentiations in a negated coordinate. For n=2, S is empty and (10) says h=0. The same statement applies later to U=(F−c_G)².

## 3. Inner reflected-star replacement

Put K₀=max(K,3). Every coordinate law used below is one of the original law of J_e, its reflection −J_e, or the standard Gaussian law. All have mean zero, variance one, fourth moment ≤K₀, third absolute moment ≤K₀^(3/4), and first absolute moment ≤1. All intermediate arrays are product laws. Reflection of a Gaussian gives the same Gaussian law; it does not introduce a common sign or dependence between coordinates.

First consider U satisfying (8), or U=F, with factor L as above. Under any such product law, with e deleted, compare the remaining star law P to its coordinatewise reflected product law P⁻. Fixing all other coordinates leaves the star independent. In any chosen order replace the |S| star coordinates one at a time. For one coordinate f, Taylor expansion of h in x_f at 0 through degree two has remainder bounded by

    C q⁶ L |x_f|³,                                     (11)

since its third derivative is ∂_f³∂_e³U, a total derivative of order six. The first two moments of a coordinate and its reflection agree, so the polynomial terms cancel in conditional expectation. Integrating over the other coordinates, each replacement costs at most C q⁶ L K₀^(3/4). The endpoints satisfy E_(P⁻)h=−E_P h by (10), with the exterior distribution unchanged. Hence

    |E h| ≤ C |S| q⁶ L ≤ C n q⁶ L.                     (12)

The 1/2 from comparing opposite expectations is absorbed into C. No sixth random-variable moment is used: six is a derivative order, while the replacement variable appears only cubically in (11). Independence justifies the conditional moment cancellation. The original and all mixed reflected/Gaussian laws remain within the same product-law class.

## 4. Outer comparison: means and smooth laws

Enumerate E and telescope from any product law described in §3 to the all-Gaussian law. At a single outer replacement e, write x for the replaced value and hold the remaining coordinates fixed. Taylor expansion of U through degree three at x=0 gives

    U(x)=U(0)+x∂_eU(0)+(x²/2)∂_e²U(0)
                  +(x³/6)∂_e³U(0)+R(x),
    |R(x)|≤ C q⁴ L |x|⁴.                              (13)

The constant, linear and quadratic terms cancel in the two conditional expectations. The cubic difference is the third-moment difference times the expectation of the deleted-edge derivative divided by six. The latter is bounded by (12); the moment difference is uniformly bounded by 2K₀^(3/4). The remainders have total expectation at most C q⁴ L K₀. Therefore one outer replacement costs at most

    C L(q⁴+nq⁶).

There are m≤n²/2 outer replacements. Since

    m q⁴ ≤ β⁴/2,        mn q⁶ ≤ β⁶/2,                 (14)

the full comparison is bounded by C L. This proves (3). With U=F, (7) gives integrability and the same Taylor estimates prove (1). In fact (1) holds simultaneously for every product law formed from {J_e,−J_e,g_e}; this uniform version is used next. The constant does not depend on the number or positions of reflections or Gaussian entries.

## 5. Variance: a finite family and two deleted coordinates

Let 𝓗 be the finite collection of all product laws choosing at each edge one of {law(J_e),law(−J_e),law(g_e)}. Duplicate choices cause no problem. Define

    M=max_(P∈𝓗) E_P[(F−c_G)²].                         (15)

M is finite by (7) and the finite second moments. The family is closed under outer replacement and reflection of any chosen star. We do not include an uncontrolled family of arbitrary deleted arrays in the maximum.

If at most r≤2 coordinates are instead set to zero, restore these coordinates independently with any compatible laws from 𝓗. Coordinatewise Lipschitz continuity gives pointwise

    |F(x with these coordinates zero)−c_G|
       ≤ |F(restored x)−c_G|+q Σ_(restored e)|x_e|.

After expectation and Cauchy–Schwarz,

    E|F(with at most r≤2 deletions)−c_G|≤√M+r q.        (16)

All applications of this bound are after averaging the exterior variables. We do not assert a uniform conditional bound by √M for every exterior realization. In the Taylor remainders below the deleted-coordinate base value is independent of the replacement variable, so unconditional (16) is exactly what is needed.

## 6. Square Taylor remainder requiring only fourth moments

Fix one edge e and all other coordinates, set

    H(z)=F(x with x_e=z)−c_G=H₀+u(z),  u(0)=0,
    b₁=u′(0), b₂=u″(0), b₃=u‴(0).

By (6), |u^(k)|≤B_kq^k. Taylor expansion gives

    |u(z)−b₁z−b₂z²/2−b₃z³/6|≤ C q⁴|z|⁴.             (17)

The key exact identity is

    u(z)²−b₁²z²−b₁b₂z³
     =2b₁z[u(z)−b₁z−b₂z²/2]+[u(z)−b₁z]².             (18)

The cubic and quadratic Taylor bounds on the two bracketed expressions, and |b₁|≤q, bound (18) by Cq⁴|z|⁴. Expanding H²=H₀²+2H₀u+u² now yields its degree-three Taylor polynomial plus remainder

    |R_sq(z)|≤C q⁴ |z|⁴(|H₀|+1).                     (19)

This avoids the spurious fifth moment that would result from bounding the fourth derivative of H(z)² at an interpolation point by a multiple of |H₀|+q|z|. Since H₀ is independent of z under a product law, (16) and the fourth-moment bound give

    E|R_sq(z)|≤C q⁴ K₀(√M+q+1).                       (20)

## 7. Cubic square coefficient under the star reflection

At e deleted put

    B=∂_e³[(F−c_G)²]
      =2(F−c_G)∂_e³F+6(∂_eF)(∂_e²F).                 (21)

By (10), B is odd under reflection of S. For another edge f∈S, applying the product rule three times to (21), and (6) to each term, gives

    |∂_f³ B|≤ C q⁶(|F−c_G|+1).                       (22)

Indeed the sole term retaining an undifferentiated F−c_G has one total sixth derivative of F; every other product consists of derivatives with total order six, so is bounded by Cq⁶. This remains true when both e and f appear repeatedly.

For z=x_f, while e remains zero, Lipschitz continuity gives

    |F(z)−c_G|≤|F(0)−c_G|+q|z|.

Taylor's integral remainder of order two, using (22) along the interval from 0 to z, is bounded by

    C q⁶[(|F(0)−c_G|+1)|z|³+q|z|⁴].                  (23)

Here F(0) has exactly e and f deleted. Its expectation is controlled by (16), and it is independent of z. Therefore each coordinate comparison with the reflected law cancels the degree-two polynomial and costs at most

    C q⁶[(√M+2q+1)K₀^(3/4)+qK₀]
       ≤ C_(β,K) q⁶(√M+1).                           (24)

The last inequality uses q≤β/√2, with β fixed. The other coordinates at every step have independent laws in 𝓗; only e and the currently expanded f are deleted in the base value. The same argument works for the two endpoint reflected choices. Telescoping the n−2 star coordinates, then using oddness, gives

    |EB|≤C n q⁶(√M+1).                               (25)

No fifth or sixth moment is present in (23)–(25). In particular the sixth derivative in (22) has not been integrated against a sixth power of a coupling.

## 8. Square comparison, bootstrap and exact centering

Telescope U=(F−c_G)² from any P∈𝓗 to Gaussian. The degree-zero, one and two Taylor terms cancel, exactly as in §4. The cubic coefficient is B/6, whose expectation is bounded by (25). The fourth remainders are bounded by (20). Thus one edge costs at most

    C(q⁴+nq⁶)(√M+1).

Using (14), for every P∈𝓗,

    |E_P[(F−c_G)²]−V|≤ C(√M+1).                       (26)

Taking a maximum over the finite class yields

    M≤V+C√M+C.

For y=√M, the quadratic formula gives

    y≤C/2+sqrt(V+C+C²/4)≤√V+C₁                       (27)

for a constant C₁ depending only on C. Substituting (27) in (26) proves

    |E_P[(F−c_G)²]−V|≤C₂(√V+1).                       (28)

By the uniform mean comparison from §4, |E_PF−c_G|≤C₃. The exact identity

    Var_P F=E_P[(F−c_G)²]−(E_PF−c_G)²

therefore turns (28) into (2). This is a genuine bootstrap over an a priori finite second moment; it never assumes the desired variance estimate for a reflected or mixed array.

## 9. Transfer of the stipulated Gaussian law

For fixed β>1, the pinned limiting-law manuscript defines precisely our uncompleted counting-prior F. Its `thm:main`, `thm:moments`, and `red:prop-moments` yield (4); the independent Gaussian completion has variance β²/2 and disappears on scale n^(1/6). No non-Gaussian completion is required here.

By (2) and (4),

    Var F(J)/V = 1+O(V^(-1/2)+V^(-1)) →1,             (29)

uniformly over the allowed array laws, so the variance is positive for all sufficiently large n. The first claim in (5) follows immediately.

Set a=√V (which is eventually ≥1) and c=c_G in (3). For each fixed real t, use separately φ(x)=cos(tx) and φ(x)=sin(tx); all their first six derivatives are bounded. Thus the characteristic functions of (F(J)−c_G)/√V and (F(g)−c_G)/√V differ by at most C_t/√V→0. The latter converges to the characteristic function of ν_β by (4). Lévy's continuity theorem gives

    (F(J)−c_G)/√V ⇒ν_β.

By (1), (EF(J)−c_G)/√V→0. Combining this with (29) and Slutsky's theorem proves the exact-own-standardization claim in (5), through all integers. Independence across different n is unnecessary.

The limiting measure ν_β retains its Gaussian-defined mean, variance, exponential moment and moment characterization as properties of that already-defined measure. The proof asserts neither convergence of all non-Gaussian finite-size moments nor exponential integrability of their pressure. Those stronger claims would be inappropriate under only a fourth-moment assumption.

## 10. Antecedents, provenance and review boundary

Ordinary coordinate replacement/Taylor cancellation, bounded-spin cumulants, and deterministic spin-gauge invariance are classical. Carmona–Hu and Chatterjee supply the direct replacement ancestry; Cheng–Liu–Shao–Xu give the especially close scaled smooth-test comparison under first-three-moment matching. The proposed additional operation is to compare the deleted cubic derivative to its reflected-star expectation by another replacement, then close the unbounded square observable through a finite hybrid maximum and the exact square remainder. The Gaussian limiting law/prefactor is entirely inherited from pinned source217; it is not proved here.

The parent supplied an author-side variance-remainder/bootstrap note before freezing, matching the feasibility direction and read independently in this lane. It is credited assistance, not an independent proof verdict. Exact primary operations and reading limits are in `217-prefreeze-comparison.md`; full source/PDF read extent and provenance will be bound in the sealed packet. No novelty certificate, self-PASS, substantiality decision, publication or campaign count is made by this proof.
