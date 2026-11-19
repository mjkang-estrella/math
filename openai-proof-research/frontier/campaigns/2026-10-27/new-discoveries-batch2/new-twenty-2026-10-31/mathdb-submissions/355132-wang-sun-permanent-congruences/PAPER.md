# Two permanent congruences for a shifted difference matrix

## Abstract

For the matrix \(B_n=[j-k+\delta_{jk}]_{1\le j,k\le n}\), we prove the two congruences conjectured by Wang and Sun. For every odd prime \(p\), its permanent in sizes \(p-1\) and \(p\) is respectively \(3\) modulo \(p\) and \(1+4p\) modulo \(p^2\). The main step in the second congruence is first-order invariance under changing the lifts of a complete residue system. A reflection fixing each coordinate in turn forces all linear terms to vanish modulo \(p\).

## Source statement

Let \(B_n\) be the integer matrix of positive size \(n\) whose \((j,k)\)-entry is \(j-k+\delta_{jk}\) for \(1\le j,k\le n\), with \(\delta_{jk}=1\) for \(j=k\) and \(0\) otherwise. Its permanent is \(\sum_{\sigma\in S_n}\prod_{j=1}^n B_n(j,\sigma(j))\). Wang and Sun conjecture, directly after (1.4) on page 3 of arXiv v8, that for **every odd prime** \(p\),
\[
 \operatorname{per}(B_{p-1})\equiv 3\pmod p,\qquad
 \operatorname{per}(B_p)\equiv 1+4p\pmod{p^2}.
\]
The MathDB record includes every prime in the first congruence. This amounts to adding \(p=2\), for which \(\operatorname{per}(B_1)=1\equiv3\pmod2\). The second remains restricted to odd primes. In fact \(B_2\) has entries \(1,-1,1,1\) in row order and permanent \(0\), whereas \(1+4\cdot2\equiv1\pmod4\). [Wang and Sun, arXiv v8](https://arxiv.org/abs/2206.12317v8)

Lean uses Mathlib's permanent. Its product fixes the column index and permutes the row index. Inverting the permutation and changing the product index gives the row-indexed formula above. The Lean matrix uses \(j+1,k+1\) as its integer labels on the zero-based type \(\mathrm{Fin}(n)\). The two added ones cancel when taking the difference, and the Kronecker delta is invariant under the change of labels.

## What was known

The source treats the determinant in (1.4) and poses the permanent congruences separately, citing a conjecture in Sun's 2021 book as motivation. Congruences and conjectures for permanents of related difference matrices use other kernels, for example Sun's conjecture \(\operatorname{per}[|j-k|]_{1\le j,k\le p}\equiv-1/2\pmod p\), and the supplied review found no earlier proof of these congruences. The rank-two expansion used below is elementary. The congruence modulo \(p^2\) also uses the reflection argument and a signed factorial sum. [Wang and Sun](https://arxiv.org/abs/2206.12317v8) · [Sun](https://arxiv.org/abs/2108.07723)

## Theorem

For every prime \(p\), \(\operatorname{per}(B_{p-1})\equiv 3\pmod p\). For every odd prime \(p\), \(\operatorname{per}(B_p)\equiv 1+4p\pmod{p^2}\). This is Wang and Sun's conjecture, with the first congruence extended to \(p=2\).

## Proof


For an integer vector \(x=(x_i)_{i\in I}\) indexed by a finite set, write \(D(x)_{ij}=x_i-x_j\). Write
\[
 F_{I,d}(x)=\sum_{\substack{S\subseteq I\\|S|=d}}\operatorname{per}D(x|_S).
\]
Use the empty permanent \(1\). Expanding \(\operatorname{per}(I+D(x))\), the rows at which the identity term was chosen must be fixed by the permutation. A permutation on the complementary set extends uniquely by fixing these rows. This gives \(\operatorname{per}(I+D(x))=\sum_{d=0}^{|I|}F_{I,d}(x)\). Each \(F_{I,d}\) is invariant under permuting the coordinates and translating them by a common value, and is homogeneous of degree \(d\). It is also invariant under negating all coordinates because \(D(-x)=D(x)^\mathsf T\), whose permanent is the same by inverting the summation permutation.

For a vector \(y\) of length \(d\), let \(e_j(y)\) denote the \(j\)-th elementary symmetric polynomial. We have the integer identity
\[
 \operatorname{per}D(y)=
 \sum_{k=0}^d (-1)^k k!(d-k)!\,e_{d-k}(y)e_k(y).
 \tag{1}
\]
Indeed, choose the \(k\) rows in which to take \(-y_{\pi(i)}\), and then choose their \(k\) image columns. For these two fixed sets there are \(k!(d-k)!\) bijections, and the products on the complementary rows and on the chosen columns are independent of those bijections. Summing over the two sets gives (1).

We use Wilson's congruence in both evaluations. Among the nonzero residues modulo \(p\), each residue pairs with its inverse unless it is its own inverse. The only self-inverse residues satisfy \((u-1)(u+1)=0\) in the field, so they are \(1\) and \(-1\). Every paired product is \(1\), and the product of the self-inverse residues is \(-1\). Hence \((p-1)!\equiv-1\pmod p\).

Fix an odd prime \(p\) and put \(m=p-1\). If \(y\) reduces bijectively to the nonzero residues modulo \(p\), the factorization of \(X^m-1\) over \(\mathbb F_p\) implies \(p\mid e_k(y)\) for \(0<k<m\) and \(e_m(y)\equiv -1\pmod p\). To see this directly, expand \(\prod_i(X-\bar y_i)\). The coefficient of \(X^{m-k}\) is \((-1)^ke_k(\bar y)\), since one must choose the constant term in exactly \(k\) factors. Each nonzero residue satisfies \(x^{p-1}=1\) by the order of the multiplicative group. Thus the monic polynomial of degree \(m\) with these roots is \(X^m-1\), and its intermediate coefficients are zero. Its constant term is \(-1\), which also gives the asserted product since \(m\) is even. The intermediate terms of (1) contain two factors divisible by \(p\) and vanish modulo \(p^2\). Since \(m\) is even, this gives
\[
 \operatorname{per}D(y)\equiv 2m!\prod_i y_i\pmod{p^2}.
 \tag{2}
\]

For the first conjectured congruence, take \(I=\{1,\ldots,m\}\) and \(x_i=i\). Multiplication by any nonzero \(u\bmod p\) permutes the reductions of \(x\). By symmetry and homogeneity,
\((u^d-1)F_{I,d}(x)\equiv0\bmod p\).
For \(0<d<m\), \(X^d-1\) has at most \(d\) roots over \(\mathbb F_p\), so some \(u\) makes \(u^d-1\) a unit. Only \(d=0,m\) remain. For \(d=0\) the sole subset is empty, giving the constant term \(1\). The sole subset of size \(m\) is the full index set. Since \(\prod_i x_i=m!\), (2) and Wilson's congruence \(m!\equiv-1\bmod p\) give \(F_{I,m}(x)\equiv2(m!)^2\equiv2\), so the sum is \(1+2=3\bmod p\). For \(p=2\), \(B_1=[1]\) and \(1\equiv3\bmod 2\).

For the second congruence use \(I=\{0,\ldots,p-1\}\), \(x_i=i\). Shifting from the source's labels subtracts \(1\) from every coordinate and preserves the matrix entries. We first show, for this \(x\), whose reductions form a complete residue system modulo \(p\), and for every \(d\), that
\[
 x'_i\equiv x_i\pmod p\ \text{for all }i
 \quad\Longrightarrow\quad
 F_{I,d}(x')\equiv F_{I,d}(x)\pmod{p^2}.
 \tag{3}
\]
Let \(F=F_{I,d}\), \(e_i\) be the \(i\)-th coordinate vector, and \(G_i(x)\) be the coefficient of \(t\) in \(F(x+t e_i)\). Fix \(i\). The reflection \(r_j=2x_i-x_j\) of the coordinates is congruent modulo \(p\) to a permutation of \(x\) that fixes \(i\). The polynomials \(F(r+t e_i)\) and \(F(x+t e_i)\) therefore agree modulo \(p\). On the other hand, common translation by \(-2x_i\) followed by negation gives the exact equality \(F(r+t e_i)=F(x-t e_i)\). The linear terms give \(G_i(x)\equiv-G_i(x)\pmod p\), so \(p\mid G_i(x)\). For \(x'=x+pb\), expansion of each monomial by the binomial theorem gives \(F(x')\equiv F(x)+p\sum_i b_i G_i(x)\pmod{p^2}\), proving (3).

For \(0<d<m\), choose \(u\) as above. The vector \(ux\) modulo \(p\) is a permutation of \(x\), so it can be reordered to apply (3). Homogeneity now gives \((u^d-1)F_{I,d}(x)\equiv0\bmod p^2\). The first factor is coprime to \(p\) and thus to \(p^2\). Bézout's identity gives its inverse modulo \(p^2\). The \(d=p\) term vanishes over the integers, since transpose yields \(\operatorname{per}D(x)=\operatorname{per}(-D(x))=-\operatorname{per}D(x)\) for odd \(p\).

For \(d=m\), omit index \(i\) and translate the remaining coordinates by \(-x_i\). Their reductions are exactly the nonzero residues. The negative differences are \(-i,\ldots,-1\) and the positive ones are \(1,\ldots,m-i\), so (2) gives
\[
 F_{I,m}(x)\equiv 2m!\sum_{i=0}^{m}\prod_{j\ne i}(j-i)
       =2m!\sum_{i=0}^{m}(-1)^i i!(m-i)!\pmod{p^2}.
\]
Let \(A_i=(-1)^i i!(m+1-i)!\) for \(0\le i\le m+1\). Using \((m+1-i)!=(m+1-i)(m-i)!\) and \((i+1)!=(i+1)i!\), the difference \(A_i-A_{i+1}\) is \((-1)^i i!(m-i)!\) times \((m+1-i)+(i+1)=m+2\) for \(i\le m\). Summing gives \((p+1)\sum_{i=0}^{m}(-1)^i i!(m-i)!=2p!\), since \(m+1\) is odd. Modulo \(p^2\) the right side is \(-2p\) by Wilson's congruence, and \((p+1)(-2p)\equiv-2p\bmod p^2\). Since \(p+1\) is relatively prime to \(p^2\), cancelling \(p+1\) gives the sum \(-2p\bmod p^2\). Consequently \(F_{I,m}(x)\equiv 2m!(-2p)\equiv4p\pmod{p^2}\). Adding the constant \(1\) finishes the proof.

## Lean correspondence

The formalization defines B and the original source proposition WangSunConjecture in namespace WangSun. It uses dual numbers \(R[\varepsilon]/(\varepsilon^2)\) to carry the constant term and the first variation together. For two dual numbers the second component of their product is \(a_0b_1+a_1b_0\). Induction on the factors of a product shows that this second component is additive in the directional coefficients. This extends to sums of products. In the reflection argument each single-coordinate direction maps to its negative, while the constant input is permuted and then translated and negated. Translation and negation invariance identify the value with its evaluation at the opposite direction. The second component therefore vanishes in \(\mathbb F_p\) for each single-coordinate direction, and additivity gives the result for arbitrary directions. Evaluation of an integer dual number \(a+b\varepsilon\) at \(\varepsilon=p\) in \(\mathbb Z/p^2\mathbb Z\) is multiplicative because \(p^2=0\) there. This is the first-order expansion (3). For the scaling argument Lean chooses a generator of the nonzero finite field elements. Its order \(p-1\) prevents \(u^d=1\) when \(0<d<p-1\).

| Proof step | Lean declarations |
| --- | --- |
| Matrix entries, source indexing and statement | B, B_zero_based, B_labels, B_positiveLabels, WangSunConjecture |
| Expand by fixed rows, then by degree | fixedEquiv, permanent_expand, sum_degrees |
| Symmetry, translation, scaling and parity | degree_reindex, degree_shift, degree_scale, degree_neg, full_odd_zero |
| Rank-two expansion and permutation count | imageFiberEquiv, image_fiber_count, image_prod_sum, complement_prod_sum, perD_rank_two |
| Nonzero residues and the top permanent | nonzeroEquiv, nonzero_poly, elem_middle_zero, perD_mod_square |
| Reflection and first-order invariance | dual_prod_add, variation_add, reflection_variation, lift_invariance |
| Intermediate degrees | exists_scale, isUnit_square, vanish_by_scaling, vanish_mod_prime, vanish_mod_square |
| Omitting one index and evaluating the top term | omitEquiv, degree_omit, prod_omit, factorial_telescope, mul_factorial_square, signed_sum_square, second_top |
| Congruences and the case \(p=2\) | first_top, first_odd, second_odd, mod_two, wang_sun_mod_prime, wang_sun_mod_prime_sq, wang_sun_source |

The endpoint checks and axiom audit from the clean compilation follow.

```text
WangSun.B_zero_based {n : ℕ} (j k : Fin n) : B n j k = ↑↑j - ↑↑k + if j = k then 1 else 0
WangSun.mod_two : (B (2 - 1)).permanent ≡ 3 [ZMOD 2]
WangSun.wang_sun_mod_prime (p : ℕ) (hp : Nat.Prime p) : (B (p - 1)).permanent ≡ 3 [ZMOD ↑p]
WangSun.wang_sun_mod_prime_sq (p : ℕ) (hp : Nat.Prime p) (ho : Odd p) : (B p).permanent ≡ 1 + 4 * ↑p [ZMOD ↑p ^ 2]
WangSun.wang_sun_source : WangSunConjecture
'WangSun.B_zero_based' depends on axioms: [propext]
'WangSun.mod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'WangSun.wang_sun_mod_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'WangSun.wang_sun_mod_prime_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'WangSun.wang_sun_source' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope of the literature review

The supplied independent AI audit searched for the source matrix, the two residues and related permanent congruences, and read the relevant passages of the arXiv v8 source and related papers by Sun, Yang and Zhang, and Jiang and Sun. It did not read Sun's 2021 Chinese-language book or any journal version of the source. Its checks of Fu–Lin–Sun and She–Sun–Xia used abstracts or snippets. The search was bounded and identified no proof of the pair. Independent numerical checks reported in the audit covered both congruences for primes below 110. This manuscript, formalization and review were AI-produced. No human peer review has taken place.

## References

- Han Wang and Zhi-Wei Sun, *Evaluations of some Toeplitz-type determinants*, arXiv v8, p. 3. [arXiv:2206.12317v8](https://arxiv.org/abs/2206.12317v8)
- Zhi-Wei Sun, *New Conjectures in Number Theory and Combinatorics* (2021), Conjecture 11.23, cited by Wang and Sun as their motivation.
- Zhi-Wei Sun, *Arithmetic properties of some permanents*. [arXiv:2108.07723](https://arxiv.org/abs/2108.07723)
- Zhi-Wei Sun, *On some determinants and permanents*. [arXiv:2207.13039](https://arxiv.org/abs/2207.13039)
- Yaoran Yang and Yutong Zhang, *Sun-type determinant and permanent congruences*. [arXiv:2605.19502](https://arxiv.org/abs/2605.19502)
- Bo Jiang and Zhi-Wei Sun, *Some new results on determinants and permanents*. [arXiv:2606.03970](https://arxiv.org/abs/2606.03970)
- Yue-Feng She, Zhi-Wei Sun and Wei Xia, *A novel permanent identity with applications*. [arXiv:2208.12167](https://arxiv.org/abs/2208.12167)
- Fu, Lin and Sun, *Permanent identities, combinatorial sequences, and permutation statistics*. [arXiv:2109.11506](https://arxiv.org/abs/2109.11506)
