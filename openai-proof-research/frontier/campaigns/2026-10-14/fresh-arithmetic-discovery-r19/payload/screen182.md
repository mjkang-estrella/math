# Vector polynomial differences: full target unresolved

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0.

## Target screened, not frozen or nominated

For every fixed d≥1 and k≥2, seek c_(d,k)>0 such that every nonconstant vector P=(P_1,...,P_d) in Z[t]^d of maximum degree k that is **jointly intersective** satisfies: there exist C_P,N_P such that, for N≥N_P, every A⊂{1,...,N}^d with (A−A)∩P(N_+)⊂{0} has |A|≤C_P N^(d−c_(d,k)). Jointly intersective means that for every modulus q a single integer t satisfies P_i(t)=0 mod q for all i. No linear independence, common integer root, coordinate sign, or full-rank restriction is imposed. There is no asserted proof or count increment. The parabola P(t)=(t,t²), a member of the target, already defeats the exact source transfer attempted here.

## Source and primary comparison

Pinned family182 manuscript `A-power-saving-for-intersective-polynomial-differences-with-an-exponent-depending-only-on-the-degree-October-5-2026`, `introduction.tex`, Theorem `thm:main`, proves the scalar assertion with exponent depending only on degree; constants C_h,N_h may depend on every coefficient, with h fixed as N grows. Its complete `tuples.tex` was read. Relevant operations:

1. Set W(y)=k^−1 # {t:F(t)=y,F'(t)≠0} on F_p. Then 0≤W≤1 and c_p=E W≥1/(2k).
2. `tuple:list-mixing` uses those pointwise bounds in edge replacement and in the fourth-moment graph argument.
3. `tuple:marking-domination` compares products by deleting factors in [0,1].
4. `tuple:laws` gives uniform single-slot marginals and an exceptional mass ≤p^−4, with polynomial increments around a fixed directed cycle outside that mass.
5. `tuple:conditional-mixing` asserts, for every mean-zero f and slot v, ||E[f(z_v) | (z_w)_(w≠v)]||_2≤p^−γ||f||_2, for γ>0 independent of p. The source uses this to control high Fourier frequencies in its later lifts.

The actual primary Lyall–Magyar paper, arXiv:0903.4504v1, §§1–2 (pages1–4), proves the monomial-curve vector assertion with density bounded by C((loglog N)^2/log N)^(1/(k−1)). Theorem3 is the vector input, not a consequence of its scalar Theorem1. Section2.1 lifts vector recurrence to simultaneous scalar polynomial configurations by a linear coefficient map and an averaged translate of A^ell. Proposition4 and §2.3 use grids with steps q,q²,...,q^k and density increments depending on the current density; the resulting iteration is logarithmic. This primary operation does not turn the new scalar power saving into a vector power saving.

## First obstruction: the scalar density and graph estimates cannot be transferred

A polynomial curve in F_p^r has ≤p points. A bounded weight supported there has mean at most p^(1−r). Hence the fixed positive lower bound on c_p is lost for r≥2. Rescaling to mean one loses W≤1, and small nonconstant Fourier coefficients alone do not repair the graph lemma.

Here is an exact example. Let p be odd, G=F_p², S={(t,t²):t∈F_p}, and W=p 1_S. Then E_G W=1. For a character indexed by (a,b),

    W_hat(a,b)=p^−1 Σ_t exp(−2πi(at+bt²)/p).

At a nonzero character this is zero if b=0 and has modulus p^−1/2 otherwise (complete the square, then use the elementary quadratic Gauss-sum identity). Nevertheless,

    E_(x0,x1,y0,y1∈G) ∏_(i,j∈{0,1}) W(yj−xi)=2−1/p.

Proof: for fixed x,x', let C(x,x') count common out-neighbors. If x=x', C=p. If x'−x=(a,b) with a≠0, subtracting the two parabola equations gives the unique parameter t=(b+a²)/(2a), hence C=1. If a=0,b≠0, C=0. Therefore Σ_(x,x') C(x,x')²=p²[p²+p(p−1)]=2p⁴−p³. Multiply by p⁴ and divide by |G|⁴=p⁸. The limit is2, whereas the mean-one graph product would be1. Thus normalized sparse curve weights cannot be substituted into `tuple:list-mixing` on the strength of Fourier decay.

This is not a counterexample to the pinned lemma: its W≤1 hypothesis has been explicitly removed in the attempted extension.

## Stronger obstruction: the source conditional-mixing property is impossible

This does not depend on the marked-block construction or the preceding graph estimate.

**Lemma.** Let p be odd, N=p², and let (Z_v) be any finite tuple of G-valued random variables, with a designated directed cycle of at least three distinct slots. Suppose every Z_v is uniform on G. Suppose there is an event E of probability at least1−η on which every consecutive cycle increment lies in S. Fix a cycle slot v and write Y=(Z_w)_(w≠v). The conditional expectation operator T:f↦E[f(Z_v)|Y] on the mean-zero subspace of L²(G) satisfies

    ||T||² ≥ [N(1−η)²/2−1]/(N−1).

A negative right side is harmless; for η=o(1), the lower bound tends to1/2.

**Proof.** Fix the two neighboring labels U,V, and write V−U=(a,b). An eligible middle label is U+(t,t²), and the outgoing increment must be (a−t,(a−t)²). Thus

    2t²−2at+a²−b=0.

There are at most two possibilities, since p is odd. For each realization y of Y, let C_y be this candidate set and q_y(x)=Pr(Z_v=x|Y=y). Set m_y=Σ_(x∈C_y)q_y(x). The event E implies Z_v∈C_Y, so E m_Y≥1−η. Cauchy–Schwarz on a set of size≤2 yields Σ_x q_y(x)²≥m_y²/2, including the empty-set case m_y=0. Jensen gives E Σ_xq_Y(x)²≥(1−η)²/2.

The N additive characters form an orthonormal basis for uniform L²(G). Conditional Parseval gives Σ_χ |E[χ(Z_v)|Y]|²=NΣ_xq_Y(x)². The constant character contributes1; each nonconstant character has uniform mean zero and norm one. Averaging over the N−1 nonconstant characters shows that at least one satisfies ||Tχ||²≥[N(1−η)²/2−1]/(N−1). This proves the lemma. The complex-character statement implies the same real operator-norm obstruction by splitting into real and imaginary parts. □

Taking η≤p^−4 rules out a bound p^−γ on ||T|| for any fixed γ>0 and all sufficiently large p. In particular, no redesigned tuple law can simultaneously retain these three exact source properties for the parabola: uniform slot marginals, cycle support outside vanishing mass, and vanishing conditional-mixing norm. Positivity was not needed for the obstruction.

## Other routes and exact remaining obligation

Encoding a box by a base B comparable to N gives the scalar polynomial h_B(t)=Σ_i B^(i−1)P_i(t). Even after solving digit carries and unwanted roots, this is a varying polynomial: the scalar theorem supplies no applicable uniform C_(h_B),N_(h_B). Choosing a fixed linear projection avoids coefficient growth but does not let a projected forbidden difference imply the full vector difference. Neither route proves the target.

A successful proof must replace the source's one-slot conditional-mixing/Fourier-lift mechanism with a genuinely vector method, or supply a coefficient-uniform encoding theorem with a correct no-carry inverse implication. Joint local roots and auxiliary progression covariance would then also need proof; they were not established in this screen. The finite-field obstruction does not imply a lower bound for avoiding sets, does not refute the target, and does not rule out anisotropic multilinear or higher-order uniformity methods. No restricted theorem is being substituted for the stated full target.
