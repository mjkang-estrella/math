# A root-of-unity proof of Guo's signed Franel power-sum congruence

## Abstract

We prove Conjecture 4.1 of Guo, arXiv:1201.0617, for every positive integer n and every nonnegative integer r. A polynomial deformation of half the desired sum vanishes at every nontrivial n-th root of unity. Its monic geometric-sum divisor descends to the integers, and specialization at 1 gives the asserted modulus 2n. The accompanying Lean certificate proves the literal statement, with no hypotheses on r beyond being a natural number. This is an implementation-stage manuscript; independent final replay and qualification remain separate campaign gates.

## Source statement and definitions

V. J. W. Guo, *Proof of two conjectures of Z.-W. Sun on congruences for Franel numbers*, arXiv:1201.0617v3, §4, p.5, introduces the definition with the words:

> For any nonnegative integers n and r, let
> \[
> f_n^{(r)}=\sum_{k=0}^n\binom nk^r.
> \]

Immediately next to this source definition, its literal Lean representation is:

```lean
def franelPow (r k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℤ) ^ r
```

The order of the two arguments is r, then k. The renaming of the source's bound variable k to j makes no change to the sum. The upper bound is inclusive in the source and is represented by `Finset.range (k+1)`. All terms, powers, and the final divisibility are over the integers. Natural exponents include zero.

Guo's Conjecture 4.1, equation (4.6), p.6, states verbatim:

> Let n ≥ 1 and r ≥ 0 be two integers. Then
> \[
> \sum_{k=0}^{n-1}(-1)^{rk}(3k+2)f_k^{(r)}\equiv0\pmod{2n}.
> \]

The theorem proved here has exactly these quantifiers and sign, including r=0. Its Lean endpoint, in namespace `Franel`, is:

```lean
theorem guo_conj_4_1 (n r : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℤ)) ∣ ∑ k ∈ Finset.range n,
      (-1 : ℤ) ^ (r * k) * (3 * (k : ℤ) + 2) * franelPow r k
```

The MathDB record 322805 reproduces this definition and congruence. It was read using the supplied corpus reader and compared to the cached arXiv v3 body before implementation. The exponent is r times k, rather than r+k or k alone. The divisibility is not a rational divisibility assertion and has a nonzero divisor under n≥1.

## Proof

## 1. Gaussian-binomial preliminaries

Write

\[
[h]_q=1+q+\cdots+q^{h-1},\qquad
{k\brack j}_q\in\mathbb Z[q],
\]

where the Gaussian binomials are defined by the polynomial Pascal recurrence

\[
{k\brack j}_q={k-1\brack j}_q+q^{k-j}{k-1\brack j-1}_q,
\]

with boundary values \({k\brack0}_q={k\brack k}_q=1\), and zero outside 0<=j<=k. In particular \({k\brack j}_1=\binom{k}{j}\). The finite q-binomial theorem, obtained by multiplying by \(1+q^{k-1}x\) and comparing coefficients, is

\[
\prod_{i=0}^{k-1}(1+q^i x)
=\sum_{j=0}^k q^{j(j-1)/2}{k\brack j}_q x^j. \tag{1}
\]

For q such that the denominator factors do not vanish, the recurrence also gives

\[
{k\brack j}_q=
\frac{\prod_{i=1}^k(1-q^i)}
 {\prod_{i=1}^j(1-q^i)\prod_{i=1}^{k-j}(1-q^i)}. \tag{2}
\]

All uses of (2) below have k<d and q of exact order d, so every displayed denominator is nonzero.

We need the standard root-of-unity q-Lucas identity, and give a derivation to make the dependency explicit. Let zeta be a primitive d-th root of unity, d>=2. If

\[
k=ud+s,\quad j=vd+t,\qquad 0\le s,t<d,
\]

then

\[
{ud+s\brack vd+t}_{\zeta}=\binom uv {s\brack t}_{\zeta}. \tag{3}
\]

Here the right side is zero when t>s. To prove (3), split the product on the left of (1) into u full blocks and one short block. Since the powers \(\zeta^i\), 0<=i<d, are exactly the d-th roots of unity,

\[
\prod_{i=0}^{ud+s-1}(1+\zeta^i x)
=\bigl(1-(-x)^d\bigr)^u\prod_{i=0}^{s-1}(1+\zeta^i x).
\]

The short factor has degree s<d. The coefficient of \(x^{vd+t}\) is zero if t>s; otherwise it equals

\[
(-1)^{v(d+1)}\binom uv\,
\zeta^{t(t-1)/2}{s\brack t}_{\zeta}.
\]

Comparing with (1) proves (3), because

\[
\zeta^{j(j-1)/2-t(t-1)/2}=(-1)^{v(d+1)}.
\]

For odd d, the exponent difference \(vd(vd+2t-1)/2\) is divisible by d and the sign is 1. For even d, use \(\zeta^{d/2}=-1\) and the fact that vd+2t-1 is odd. This covers both parities of d and requires no primality assumption.

## 2. The deformation

For r>=1 define the Laurent polynomial

\[
R_{n,r}(q)=\sum_{k=0}^{n-1}\sum_{j=0}^{k}
 (-1)^{rk}q^{\,n-1-k-rk(k+1)/2}
 {k\brack j}_q^r [k+j+1]_q. \tag{4}
\]

The exponent k(k+1)/2 is an integer. Multiplication by \(q^{rn(n-1)/2}\) clears every negative exponent: in each resulting term the exponent is

\[
n-1-k+r\bigl(n(n-1)-k(k+1)\bigr)/2\ge0.
\]

Thus

\[
P_{n,r}(q):=q^{rn(n-1)/2}R_{n,r}(q)\in\mathbb Z[q]. \tag{5}
\]

At q=1, binomial symmetry j<->k-j gives

\[
\begin{aligned}
2\sum_{j=0}^k(k+j+1)\binom{k}{j}^r
 &=\sum_{j=0}^k\bigl((k+j+1)+(2k-j+1)\bigr)\binom{k}{j}^r\\
 &=(3k+2)f_k^{(r)}.
\end{aligned} \tag{6}
\]

Consequently twice \(P_{n,r}(1)=R_{n,r}(1)\) is the source's integer sum. It will suffice to prove

\[
[n]_q\mid P_{n,r}(q)\quad\hbox{in }\mathbb Z[q]. \tag{7}
\]

This also explains why proving only divisibility of the full deformed sum by [n] is unnecessarily awkward: (4) already deforms an integer half of it.

## 3. Cancellation at a primitive root

Let zeta be a primitive d-th root, d>=2. First take n=d. In each term of (4), put

\[
a=j,\qquad b=k-j,\qquad c=d-1-k.
\]

These triples run once through all nonnegative solutions a+b+c=d-1. Formula (2) gives

\[
{d-1\brack k}_{\zeta}=(-1)^k\zeta^{-k(k+1)/2}. \tag{8}
\]

Indeed the numerator in the product expression is
\(\prod_{i=1}^k(1-\zeta^{-i})\), and
\(1-\zeta^{-i}=-\zeta^{-i}(1-\zeta^i)\).

It follows that

\[
(-1)^{rk}\zeta^{-rk(k+1)/2}{k\brack a}_{\zeta}^{r}
=T(a,b,c)^r,
\]

where

\[
T(a,b,c)=
\frac{\prod_{i=1}^{d-1}(1-\zeta^i)}
 {\prod_{i=1}^{a}(1-\zeta^i)
  \prod_{i=1}^{b}(1-\zeta^i)
  \prod_{i=1}^{c}(1-\zeta^i)}. \tag{9}
\]

This expression is symmetric in a,b,c. All denominator factors are nonzero, since each coordinate is at most d-1. Also k+j+1=2a+b+1=d+a-c, so

\[
\zeta^c[k+j+1]_{\zeta}
=\frac{\zeta^c-\zeta^{d+a}}{1-\zeta}
=\frac{\zeta^c-\zeta^a}{1-\zeta}. \tag{10}
\]

Substituting (9)–(10) into (4) gives

\[
R_{d,r}(\zeta)=\frac1{1-\zeta}
\sum_{a+b+c=d-1}(\zeta^c-\zeta^a)T(a,b,c)^r=0. \tag{11}
\]

The last equality is an exact finite cancellation under the involution (a,b,c)<->(c,b,a). Fixed points a=c have zero summand. This is the structural cancellation missing from the composite-n integer proof.

## 4. Every divisor of n, not just the primitive n-th roots

Let d>=2 divide n, write n=Nd, and retain a primitive d-th root zeta. Partition the summation (4) by

\[
k=ud+s,\qquad j=vd+t,
\qquad 0\le u<N,\quad 0\le s,t<d.
\]

When t>s, (3) makes the Gaussian coefficient zero; the assumption r>=1 is used here. The surviving terms have 0<=v<=u and 0<=t<=s. For them (3) gives the factor \(\binom uv^r{s\brack t}_{\zeta}^r\). The q-integer satisfies

\[
[k+j+1]_{\zeta}=[s+t+1]_{\zeta}, \tag{12}
\]

since the two lengths differ by a multiple of d. Their positive lengths need not be less than d; the identity follows directly from the geometric-sum formula.

The remaining phase splits as

\[
(-1)^{rk}\zeta^{n-1-k-rk(k+1)/2}
=(-1)^{ru}(-1)^{rs}
\zeta^{d-1-s-rs(s+1)/2}. \tag{13}
\]

For completeness, \(n-1-k-(d-1-s)=(N-u-1)d\). For the triangular part,

\[
\frac{k(k+1)-s(s+1)}2=\frac{ud(ud+2s+1)}2.
\]

If d is odd, u(ud+2s+1) is even, so the zeta-power from this difference is 1 and \((-1)^{r ud}=(-1)^{ru}\). If d is even, \((-1)^{r ud}=1\), while \(\zeta^{-r ud(ud+2s+1)/2}=(-1)^{ru}\) because ud+2s+1 is odd. This proves (13) without overlooking even d, including d=2.

Equations (3), (12), and (13), with the stated surviving index ranges, yield the exact block factorization

\[
R_{n,r}(\zeta)=
\left(\sum_{u=0}^{N-1}(-1)^{ru}\sum_{v=0}^{u}\binom uv^r\right)
R_{d,r}(\zeta)=0. \tag{14}
\]

Thus (5) vanishes at **every** nontrivial n-th root of unity.

## 5. Integral divisibility and specialization

For n>=2 the polynomial \([n]_q=(q^n-1)/(q-1)\) is monic of degree n-1 and has precisely the n-1 distinct nontrivial n-th roots of unity as its roots over the complex numbers. Polynomial division by this monic polynomial can be performed inside Z[q]:

\[
P_{n,r}=[n]_q Q+H,\qquad Q,H\in\mathbb Z[q],\quad\deg H<n-1.
\]

At all those n-1 distinct roots, (14) gives H=0. A nonzero polynomial of degree less than n-1 cannot have n-1 distinct roots; hence H=0. This proves (7) **over the integers**, not merely over the rationals. For n=1, [1]=1 and the same divisibility is immediate.

Evaluating at q=1 gives \(n\mid P_{n,r}(1)\) in Z. Multiplying by 2 and applying (6) proves

\[
2n\mid\sum_{k=0}^{n-1}(-1)^{rk}(3k+2)f_k^{(r)}
\]

for every r>=1 and n>=1.

Finally, for r=0, \(f_k^{(0)}=k+1\) and the elementary telescoping identity

\[
\sum_{k=0}^{n-1}(3k+2)(k+1)=n^2(n+1)
\]

follows from \((k+1)^2(k+2)-k^2(k+1)=(3k+2)(k+1)\). The right side is divisible by 2n because n(n+1) is even. This covers r=0, n=1, even n, prime powers, and arbitrary composite n. There is no residual lifting step.


## Prime sanity theorem

For a prime p, write m=p−1. Pascal's identity and p dividing C(p,k) for 0<k<p give C(m,k)≡(−1)^k modulo p. The product M(k,j)=C(m,k)C(k,j) is unchanged under (k,j)↦(m−j,m−k), since both expressions equal the multinomial with coordinates j,k−j,m−k. Modulo p, the weight k+j+1 equals j−(m−k). Therefore the sum defining half the source expression is the difference of two equal sums under that bijection, so p divides it. Doubling gives the modulus 2p. This argument includes p=2 and r=0, uses no division by 2, and is formalized as `guo_prime`. It does not supply a lift to composite n.

## Formal implementation and verification

The certificate contains internal Gaussian polynomials: `rect` is a Pascal recursion indexed by the column and its complement, and `gauss n k` uses it inside 0≤k≤n and is zero outside. `gauss_succ_succ` verifies the row/column Pascal recurrence used above; `gauss_eval_one` proves the bridge to the source's actual `Nat.choose`. The factorial identity and generating coefficients are proved from that recursion. The Gaussian foundations and generating-product proof were adapted from the supplied Catalan formalization lane, copied into this packet, and rebuilt locally. No other lane's compiled objects are dependencies.

The Lean polynomial `deformation n r` uses exponent
\[
n-1-k+r\bigl(\operatorname{tri}(n)-\operatorname{tri}(k+1)\bigr),
\quad \operatorname{tri}(h)=h(h-1)/2.
\]
For k<n, this is nonnegative. `deformation_eval` proves that its value at a nonzero complex number z is z^(r·tri(n)) times the rational-expression finite sum R in (4), and `deformation_eval_one` identifies its value at 1 with the integer `halfSum`. The pairing identity is proved separately as `twice_halfSum`; no equivalence is left solely to the manuscript.

The implementation keeps both parity signs through the identity
\[
\zeta^{\operatorname{tri}(d)}=(-1)^{d+1}.
\]
It follows from the constant coefficient of the product over all d-th roots. An odd-order phase prototype is retained, and `phase_block` proves (13) for both parities. `cgen_full` proves the product 1−(−x)^d; coefficient extraction through polynomial expansion gives `qLucas`, including the zero-carry cases. The Gaussian top-row formula is also obtained by coefficient recursion, avoiding singular division at a root of unity.

For primitive-order cancellation, `gval_kernel` expresses the evaluated product of two Gaussians as a symmetric three-factor quotient with nonzero denominators. `triangle_swap` proves the exact finite-index involution. `primitive_vanish` uses equality of the two coordinate-weighted sums, rather than deducing cancellation by dividing an equality by 2.

For the divisor-block step, `rootSum_rect` extends j≤k to the rectangular range j<n using the zero extension and r>0. `sum_blocks` splits each rectangular range into u*d+s. Thus all four index ranges are independent. q-Lucas, `phase_block`, and `qval_block` factor each summand. Terms with v>u or t>s vanish; extending/restricting the binomial rows is justified by `choose_sum_extend`. The result is `rootSum_block`, exactly (14), including N=0.

For the final integer step, `qInt_dvd_of_vanish` maps to complex polynomials. The geometric-sum polynomial divides X^n−1 and is separable, so its roots all have multiplicity at most 1. Root inclusion implies polynomial divisibility over the complexes. Mathlib's `Polynomial.map_dvd_map` descends it to integer coefficients using monicity; internally this is division by a monic polynomial and injectivity of the coefficient map. This is equivalent to the integer remainder argument above. The certificate proves the integer cyclotomic-factor divisibilities as consequences of this result and the product formula for the cyclotomic factors; it does not need to assume a minimal-polynomial bridge.

`Franel.guo_conj_4_1` depends only on `propext`, `Classical.choice`, and `Quot.sound`. The source appendix is byte-identical to the source modules and includes the complete definitions and all bridges. The packet includes the pinned tools, build receipts, axiom outputs, and an author-side clean extraction/rebuild with a standalone kernel check of every module. No computation tactic using an external native oracle occurs. The bounded small-case congruence theorem uses ordinary `decide` and is supplementary to the unbounded proof.

## Prior art and limits

The independent pre-Lean reviewer, Claude Opus 5.5, examined the full ordinary proof and compared the record with arXiv v3. The following paragraph is reproduced from that review (the first-person reader is the reviewer):

> arXiv 1201.0617 v1, v2 and v3 all keep Conjecture 4.1; I read v3 Section 4. The journal version is Integral Transforms Spec. Funct. 24 (2013) 532–539, and the publisher refused the earlier lane with a 403. Its abstract, read through Semantic Scholar, matches the arXiv abstract. The journal DOI dates from 2012, consistent with v3 (July 2012) being the accepted text. Flag JOURNAL_TEXT_UNREAD, low risk.

The final statement review on 20 November 2026 independently compared all three arXiv versions and found the same literal endpoint, including r=0 and r=1. It found no mathematical gap in the written argument. Independent bounded computation checked 1≤n≤60 and 0≤r≤8, and checked the integral polynomial divisibility for 1≤n≤12 and 1≤r≤5. These computations support the exposition and do not replace its proof.

Prior-art qualification remains unresolved. Zhang and Yuan, *Proof of three divisibilities of Franel numbers and binomial coefficients*, IJNT 16 (2020), 1535–1546, DOI https://doi.org/10.1142/S1793042120500797, has a publicly visible publisher preview on ResearchGate and an abstract reproduced in OpenAlex. They describe three confirmations attributed to Guo and Zeng and additional polynomial-sequence results, but the accessible preview does not show the three statements. The authorship phrasing alone cannot exclude the present conjecture or a theorem implying it. No full text or substantive review was obtained; the source journal body also remains unread. This packet is therefore a correct-proof candidate, not yet cleared for a public claim of resolving a previously open problem.

The final review's two Omega issue searches and corresponding two PR searches returned no hits, as did two bounded GitHub code searches. The specified local Principia, mio-qwq, omega and openai/math clones had no relevant statement hit; this does not assert that their current live contents were exhaustively searched. Guo's source already proves the cases r≤3, and the later accessible papers inspected still concern fixed cubic Franel numbers or different binomial sums. The closest methodological antecedent inspected is Guo–Zeng, arXiv:1008.2894, using q-Lucas and root-of-unity blocks for other sums. No refused route was bypassed.

The mathematical contribution asserted is the particular deformation of half the sum, its symmetric cancellation at roots of unity, and the resulting arbitrary-r congruence. The tools are classical, and this is a modest q-congruence result. The source already proves small r cases; the prime sanity theorem and those parameter cases are not separately claimed as discoveries. A specialist may judge the construction routine. A complete certificate establishes correctness relative to the pinned trusted library, not worldwide priority or campaign acceptance. Independent final statement review, extracted replay, and any remaining qualification decisions belong to the root pipeline.

## References

1. V. J. W. Guo, *Proof of two conjectures of Z.-W. Sun on congruences for Franel numbers*, arXiv:1201.0617v3 (21 July 2012), §4, Conjecture 4.1, (4.6). https://arxiv.org/abs/1201.0617v3 . Journal DOI: https://doi.org/10.1080/10652469.2012.715160 . Journal body not read.
2. H. Zhai, B. He and L. Li, *Some Congruences on q-Franel Numbers and q-Catalan Numbers*, Indian J. Pure Appl. Math. 50 (2019), 181–189; q-Lucas and distinct prime-row results as recorded in the supplied review.
3. The supplied internal proof and cross-model review are hashed in `input-provenance.json`. The review's access limits and uncertainty are retained above.
