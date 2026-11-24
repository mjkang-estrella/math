# A conditional kernel-checked proof of the multiset Euler–Mahonian factorisation conjecture

The result is kernel-checked modulo the source's published formula, which
enters as the named hypothesis `H_published_CarnevaleTielker_formula10 :
SourceFormula10`. The theorem `source_conjecture_351584` proves the full E2
endpoint for MathDB 351584: both directions of the source-general unitary
factor classification, and the printed integral factorization with a cofactor
having no unitary factor. Everything after that single published identity is
proved in Lean. The identity itself is not proved here or installed as an axiom. Thus the
Lean result is conditional on a published theorem, not an unconditional
formal derivation from the literal word definitions.

All 49 stage-3 modules are retained byte-identically. Seven additional modules
complete the general unitary reduction and final assembly. Simion's theorem,
Kronecker's theorem and general reciprocity are not assumed or used. The
proof works with the literal Denert/excedance polynomial over Z[x,y].
REPORT.md contains the exact statements, axiom outputs and runner receipts.

## Printed statement and literal definitions

Source: Angela Carnevale and Elena Tielker, *On Denert's statistic*, Electronic
Journal of Combinatorics 29(3) (2022), #P3.1, DOI 10.37236/11013; arXiv:2108.04700v1.
The journal source is cached at the path and hash in SOURCE-RECEIPTS.json.
Page and statement references here are to that journal PDF, not arXiv numbering.
Mathematical expressions in the quotations are typeset afresh; the words are
transcribed from the source, repairing PDF extraction of inequality symbols.

Page 2, §2:

> Given η, we let Sη denote the set of all permutations of the multiset
> {1,…,1,…,r,…,r} comprising η₁ copies of 1, η₂ copies of 2, and so on.
> In other words, a multiset permutation in Sη is a rearrangement of the
> “trivial” word idη = 1^{η₁} ⋯ r^{ηᵣ} ∈ Sη.

Lean: `baseFrom 1 η` concatenates these blocks. `multisetPerms η` takes the
finite set of rearrangements, discarding enumeration duplicates. The theorem
`mem_multisetPerms` proves exactly `w ∈ multisetPerms η ↔ w.Perm (baseWord η)`;
`word_length` proves that every such word has length η.sum. No word with an
incorrect count is admitted.

Page 3, equation (1):

> A position i ∈ [n] is an excedance of w ∈ Sη if the i-th letter of w is
> strictly greater than the i-th letter of the trivial word id.

The printed equations are `Exc(w) = {i ∈ [n] : wᵢ > idᵢ}` and
`exc(w) = |Exc(w)|`. Lean stores indices 0,…,n−1 in `excPositions` and takes
its cardinality in `exc`. The conversion to printed positions occurs in `den`
by summing i+1. `getD 0` is a total list-access operation, but all counted
indices are in the word's range; `word_length` also certifies the trivial word's
length on `Sη`.

Definition 1, page 3:

> The exceeding subword of w is exc(w) := w_{i₁} ⋯ w_{iₖ} for
> Exc(w) = {i₁,…,iₖ}<. The non-exceeding subword of w is
> nexc(w) := w_{j₁} ⋯ w_{j_{n−k}} for {j₁,…,j_{n−k}}< := [n] ∖ Exc(w).

Lean: `exceedingWord` and `nonExceedingWord` filter `w.zipIdx`, preserving order.
The source's inversion formula is
`inv(w) = |{(i,j) : 1 ≤ i < j ≤ n, wᵢ > wⱼ}|` and its weak version is
`imv(w) = |{(i,j) : 1 ≤ i < j ≤ n, wᵢ ≥ wⱼ}|`.
Lean `inv` and `imv` filter the full product of bounded index sets and impose
exactly these comparisons. In particular the weak comparison is not replaced
by the strict one.

Definition 2, page 3:

> Let w ∈ Sη. Denert’s statistic on multiset permutations is given by
> den(w) := ∑_{i∈Exc(w)} i + imv(exc(w)) + inv(nexc(w)).

Lean `den` is precisely this sum. The kernel checks the source example
`den [3,2,2,3] [4,2,3,2,3,1,4,1,4,1] = 27` and both source subwords.
The literal `denertPoly` is the sum of `x ^ den η w * y ^ exc η w` over
`multisetPerms η` in `MvPolynomial (Fin 2) ℤ`; x is variable 0 and y variable 1.
It is not defined using descents or major index.

Page 19, §6.2:

> A nonconstant polynomial f ∈ ℤ[x,y] is called unitary if there exists
> F ∈ ℤ[Y] such that f(x,y) = F(xᵃyᵇ) for some a,b ∈ ℕ₀ and all complex
> roots of F have absolute value 1.

Lean `IsUnitary` includes nonconstancy, natural exponents allowing zero, and
`∀ z : ℂ, Polynomial.eval₂ (Int.castRingHom ℂ) z F = 0 → ‖z‖ = 1`.
`HasUnitaryFactor` means divisibility in the actual integer bivariate ring.
`binomial_isUnitary` already proves the predicate for each `1+x^a*y`.

Conjecture 23, page 19, verbatim:

> Let η be a composition. Then the polynomial of the joint distribution
> of (den,exc) over Sη has a unitary factor if and only if η = (mʳ) is a
> rectangle, with r even and m odd. In this case,
>
> ∑_{w∈Sη} x^{den(w)} y^{exc(w)} = (1+x^{rm/2}y) f₀^η(x,y)
>
> where f₀^η(x,y) has no unitary factor.

Lean `Conjecture23` quantifies over all nonempty lists of positive parts,
requires positive m and r for rectangle witnesses, and states both this
biconditional and the displayed factorization with the no-unitary-factor
quotient clause. `rectangleFactor η.sum` is exactly `1+x^(η.sum/2)*y`.
The exact Lean statement is reproduced in REPORT.md and the source appendix.

The inherited source packet also includes the inspected companion paper: A. Carnevale and C. Voll, *Orbit Dirichlet
series and multiset permutations*, Monatsh. Math. 186 (2018), 215–233,
DOI 10.1007/s00605-017-1128-9, cached journal PDF. Its §2.2 defines
`Cλ(x,q)=∑_{w∈Sλ}x^{des(w)}q^{maj(w)}`; equation (2.3) is MacMahon's
formula used below. Conjecture B on page 223 reads:

> Let λ = (λ₁,…,λₘ) be a partition. Then Cλ(x,q) has a unitary
> factor if and only if λ = (rᵐ) is a rectangle, with r odd and m even.
> In this case, C_{r,m}(x,q) = (1+xq^{rm/2}) C′_{r,m}(x,q)
> and C′_{r,m}(x,q) has no unitary factor.

Its part-size/count letters and variable order differ from those of Conjecture 23.
The Lean definitions follow Conjecture 23, as does MathDB 351584.
The MathDB 351584 prose omits the source's word “nonconstant”; it must be
read with that source convention. Constant units are not unitary factors.
A nonconstant monomial also fails the definition: its representing
nonconstant monomial polynomial has a root at zero, not on the unit circle.

The same mathematical result resolves MathDB 333538 through Han's
published identity (Carnevale–Tielker, Theorem 3):
`D_eta(q,t) = sum_w q^maj(w)*t^des(w) = C_eta(t,q)`.
Restricting compositions to partitions and exchanging the two variables
transports divisibility, the general unitary predicate, and the cofactor
clause. The part size is odd and the number of parts is even in both
notations. The present Lean endpoint defines no descent/major-index
polynomial and proves no transfer theorem for 333538; that last transfer
uses the published identity outside Lean. These are duplicate formulations
of one mathematical resolution, not two independent discoveries.

## The single published-formula hypothesis

Theorem 3, page 4, identifies the (den,exc) polynomial with the (maj,des)
polynomial. Theorem 10 identifies the numerator for η-admissible permutations
with the same literal polynomial. Equation (10), page 19, prints

\[
W_η(x,y)=(1-x^n y)\mathop{\bigodot}_{i=1}^r W_{(η_i+1)}(x,y)
=(1-x^n y)\mathop{\bigodot}_{i=1}^r
 \left(\frac{1}{\prod_{0≤j≤η_i}(1-x^j y)}\right),
\]

where the Hadamard product is with respect to y. The numerator description
preceding Corollary 13 is `Wη = Dη / ∏_{j=0}^{n−1}(1-x^j y)`.
Thus the exact numerator form is

\[
D_η(x,y)=\prod_{j=0}^{n}(1-x^j y)
 \mathop{\bigodot}_{i=1}^r\left(\prod_{j=0}^{η_i}(1-x^j y)\right)^{-1}.
\]

This is `SourceFormula10At η`; its universal positive-composition form is
`SourceFormula10`. Each inverse is the formal series inverse with constant
coefficient 1, constructed as `PowerSeries.invOfUnit`. Hadamard means a
coefficientwise product; its empty product has every coefficient equal to 1,
not the multiplicative identity of the power-series ring.
This identity is an explicit hypothesis, not an axiom declaration, opaque
bridge, root-preserver hypothesis, or redefinition of Dη. The full identity
is kernel checked for [1] and [2], and the two-letter polynomial is computed
literally as `1+x*y`. These are transcription safeguards, not a proof of the
universal published identity. Proving that identity itself still requires
Han's equidistribution and the barred-word/MacMahon argument; this stage does
not claim it is a small extra task.

## Complete written proof as formalized

From the formal Hadamard identity and the Gaussian-binomial generating
identity (proved as M1),
\[
\frac{A(t,q)}{\prod_{h=0}^{N}(1-tq^h)}
 =\sum_{k≥0}t^k\prod_i{k+η_i\brack η_i}_q.
\]
Here the Gaussian identity follows by induction from the finite product
`∏_{j=0}^m(1-q^j t)⁻¹`, or its Pascal recurrence. This is an algebraic
consequence of the sole named hypothesis. Throughout, A is the image of the
literal Denert polynomial in the indicated coefficient ring.


Write A(t,q)=Dη(q,t). The published formula gives A(0,q)=1. At q=0, every Gaussian coefficient in the coefficient series is 1, while the finite denominator becomes 1−t; hence A(t,0)=1.

### 1. General unitary divisors: the endpoint-arc reduction

Suppose the nonconstant f=F(q^a t^b) divides A. The two axis identities
force a,b>0: otherwise f would divide 1 after a specialization fixing f,
hence would be a constant unit. Evaluating the divisibility at the origin
gives F(0)=±1. At (q,t)=(1,1), A is the positive number of multiset words
(the increasing word belongs to the set), so F(1) is nonzero.

Use the finite identity (3) below in its polynomial form
E A = sum_j c_j product_{k≠j}(1-tq^k). It descends by injectivity from
Q(q)[t] to Q[q,t], so it can be evaluated at any complex q,t, even if E or
a displayed rational denominator vanishes there. If A vanishes and exactly
one factor 1-tq^i is zero, then c_i must be zero. This is impossible at
i=0, since c_0=1, and at i=N if q≠0, since c_N is a signed power of q.

Choose any complex root rho of F. It has norm 1 and is not 1. Write
rho=exp(i theta), -pi<theta≤pi, theta≠0. For any positive integer d,
Q=exp(i theta/d) satisfies Q^d=rho and Q≠0. If 0<j<2d then Q^j≠1:
otherwise theta*j/d would be a nonzero integral multiple of 2pi, whereas
its absolute value is strictly less than 2pi. This elementary short-arc
lemma uses `Complex.exp_eq_one_iff`, not a roots-of-unity theorem.

If 2a>N, choose d=a and t=1. Then F(Q^a)=0 makes A(1,Q)=0,
and j=0 is the unique zero denominator. The endpoint contradiction gives
2a≤N. Set d=bN-a>0. Apply the same arc lemma to rho inverse, giving
Q^d=rho inverse. At t=Q^(-N), Q^a*t^b=rho, so A vanishes. If
2d>N, the only vanishing denominator is j=N: another would force
Q^(N-j)=1 with 0<N-j<2d. Thus 2(bN-a)≤N. Since b≥1, these bounds
force b=1 and N=2a.

At this equality choose Q^a=rho as before. A second zero denominator at
t=1 could occur only at j=N=2a. That would give rho squared=1, hence
rho=-1 because rho≠1. Therefore every root of F is -1. F is nonconstant,
so FTA gives a root. Splitting over C and multiplying its root factors
writes F=c(1+Y)^e; evaluating at 0 gives c=F(0)=±1. Injectivity of the
integer-to-complex polynomial map descends this identity to Z[Y]. Here e>0
because f is nonconstant. The no-square argument in §6 below excludes
e≥2 after substitution. Therefore f=±(1+q^a t). This proves U1 without
Simion, Kronecker, primitive-root lifting, or an extra cited hypothesis.

### 2. A rational-function identity and the midpoint reduction

Define

\[
 C(z;q)=\prod_i\prod_{s=1}^{\eta_i}(1-q^s z)
       =\sum_{j=0}^{N}c_j(q)z^j,
 \qquad E(q)=\prod_i\prod_{s=1}^{\eta_i}(1-q^s).
\]

Expanding the q-binomial coefficients in the displayed MacMahon identity and summing geometric series yields the rational identity

\[
 \frac{A(t,q)}{\prod_{h=0}^{N}(1-tq^h)}
 =\frac1{E(q)}\sum_{j=0}^{N}\frac{c_j(q)}{1-tq^j}.
 \tag{3}
\]

This is an identity over ℚ(q)(t), so no analytic convergence hypothesis is involved. After t=−q⁻ᵃ all factors E and 1+q^{h−a} are nonzero elements of ℚ(q). Therefore

\[
 A(-q^{-a},q)=0\quad\Longleftrightarrow\quad
 L_a(q):=\sum_{j=0}^{N}\frac{c_j(q)}{1+q^{j-a}}=0.
 \tag{4}
\]

If a>N/2, let ζ be a primitive 2a-th root of unity. A denominator in (4) vanishes precisely when j−a is an odd multiple of a. Since 0≤j≤N<2a, only j=0 qualifies. The corresponding term is qᵃ/(1+qᵃ), since c₀=1, and it has a genuine simple pole at ζ. Every other term is regular there. This contradicts Lₐ=0. Hence a≤N/2.

For the opposite inequality, suppose N>2a and take a primitive
2(N-a)-th root zeta. Only the top denominator q^a+q^N vanishes:
q^N=-q^a, while 0≤j<N<2(N-a) and primitive-root injectivity excludes
any other j with q^j=-q^a. The top coefficient is a signed monomial and
is nonzero at zeta. Clear the polynomial denominators first, isolate that
term, and obtain a contradiction. Thus N≤2a and hence

\[
N=2a. \tag{6}
\]

In particular N is even. This also excludes every odd total size, not just a tested range.

### 3. Two necessary pole conditions

Assume N=2a. Set

\[
 S=\sum_i\frac{\eta_i(\eta_i+1)}2,
 \qquad H(q)=\sum_i\sum_{s=1}^{\eta_i}q^s.
\]

The four coefficients needed are

\[
 c_0=1,\quad c_N=q^S,\quad c_1=-H(q),\quad
 c_{N-1}=-q^S H(q^{-1}). \tag{7}
\]

At a primitive N-th root ζ, only j=0,N in (4) have vanishing denominators. Their sum is

\[
 \frac{q^a+c_N(q)}{1+q^a}.
\]

Its pole must cancel. Since ζᵃ=−1, (7) implies ζˢ=1, and hence

\[
 N\mid S. \tag{8}
\]

Suppose now N≥4, so a≥2, and let ξ=exp(2πi/(N−2)). Here 1+q^{j−a} vanishes only for j=1,N−1. Indeed j−a must be an odd multiple of a−1, and 3(a−1)>a for a≥2. The sum of these two terms is

\[
 \frac{q^{a-1}c_1(q)+c_{N-1}(q)}{1+q^{a-1}}.
\]

Cancellation at ξ, using ξ^{a−1}=−1, gives

\[
 H(\xi)=\xi^S H(\xi^{-1}). \tag{9}
\]

Write S=Nℓ with ℓ∈ℤ by (8). Since ξ^{N−2}=1, equation (9) becomes

\[
 H(\xi)=\xi^{2\ell}H(\xi^{-1}).
\]

Because H has real coefficients and |ξ|=1, this asserts that ξ⁻ˡH(ξ) is real. In particular

\[
 \sum_i\sum_{s=1}^{\eta_i}
 \sin\!\left(\frac{2\pi(s-\ell)}{N-2}\right)=0.
 \tag{10}
\]

The next lemma makes (10) impossible for a nonrectangle.

### 4. The strict sine-sum lemma (new step)

**Lemma.** Let m₁,…,mᵣ be positive integers, not all equal, set

\[
 N=\sum_i m_i,\qquad M=\frac{\sum_i m_i^2}{N},
 \qquad \mu=\frac{M+1}{2}.
\]

For every real z with 0<z and z·maxᵢmᵢ≤π,

\[
 \sum_i\sum_{s=1}^{m_i}\sin(2z(s-\mu))<0. \tag{11}
\]

**Proof.** Put sinc(x)=sin(x)/x for x≠0 and sinc(0)=1. This function is even and strictly decreasing from 1 to 0 on [0,π]. For example, the derivative numerator sin x−x cos x is positive on (0,π), because its derivative is x sin x>0 and its value at zero is zero.

We also need, for u,v>0 with u+v<π,

\[
 \operatorname{sinc}(u)\operatorname{sinc}(v)
 >\operatorname{sinc}(u+v). \tag{12}
\]

After multiplying by the positive denominator uv(u+v), the difference in (12) has numerator

\[
 (u+v)\sin u\sin v-uv\sin(u+v).
\]

Dividing this numerator by the positive quantity uv sin u sin v leaves

\[
 (1/u-\cot u)+(1/v-\cot v)>0;
\]

each summand is positive by sin x−x cos x>0. This proves (12).

The elementary finite sine-sum formula gives

\[
 \sum_{s=1}^{m}\sin(2z(s-\mu))
 =\frac{\sin(mz)\sin((m-M)z)}{\sin z}
 =\frac{z^2}{\sin z}\,m(m-M)B(m),
 \quad B(m)=\operatorname{sinc}(mz)\operatorname{sinc}((m-M)z).
 \tag{13}
\]

The hypotheses and nonconstancy imply max mᵢ≥2, so 0<z≤π/2 and sin z>0. Also M is a strict weighted mean of the mᵢ with positive weights mᵢ/N; hence 0<M<max mᵢ and Mz<π.

If 0<m<M, apply (12) with u=mz and v=(M−m)z, using evenness of sinc, to obtain B(m)>sinc(Mz). If m>M, strict decrease gives sinc(mz)<sinc(Mz), while 0≤sinc(mz) and 0<sinc((m−M)z)≤1. Thus B(m)<sinc(Mz), including the endpoint mz=π. It follows that

\[
 m(m-M)\bigl(B(m)-\operatorname{sinc}(Mz)\bigr)<0
 \quad\text{whenever }m\ne M.
\]

Finally ∑ᵢmᵢ(mᵢ−M)=0 by the definition of M, and at least one mᵢ differs from M. Summing (13) therefore gives a strictly negative result. This proves (11). ∎

### 5. Excluding every nonrectangular composition

A one-part composition has A=1 and no unitary divisor, so assume r≥2. In the situation of (6), N≥4 unless N=2, which is treated separately below.

If max ηᵢ=N−1, the list of parts is (N−1,1) in some order, and

\[
 S=N(N-1)/2+1\equiv N/2+1\pmod N.
\]

For even N≥4, 0<N/2+1<N, contradicting (8). Therefore every still possible nonrectangular list satisfies max ηᵢ≤N−2.

Apply the lemma with mᵢ=ηᵢ and z=π/(N−2). Its angle hypothesis holds, including equality when a part is N−2. Moreover

\[
 \mu=\frac12\left(\frac{\sum_i\eta_i^2}{N}+1\right)
     =\frac{S}{N}=\ell.
\]

Thus the left side of (10) is strictly negative, contradicting (10). Every composition with a unitary factor is consequently a rectangle.

For η=(mʳ), condition (8) reads

\[
 S/N=(m+1)/2\in\mathbb Z,
\]

so m is odd. Since N=rm is even, r is even as well. This proves the entire necessity direction for N≥4. If N=2, the only compositions are (2), with A=1, and (1,1), with A=1+tq; these agree with the theorem. N=1, and all odd N, were already excluded.

### 6. Multiplicity, rectangle existence, and integral descent

Multiplicity one is proved without a simple-root theorem. Let
D(t)=∏_{j=0}^N(1−tq^j) and P_j(t)=D(t)/(1−tq^j), where P_j is defined
as a polynomial product with one factor omitted. The proved source bridge is
A=Σ_j(c_j/E)P_j. Differentiating D=(1−tq^j)P_j gives the polynomial identity
D P_j′−D′ P_j=q^j P_j². If A(t₀)=A′(t₀)=0 at t₀=−q^(−a), the
nonzero denominator values give Σ_j c_j q^j/(1+q^(j−a))²=0.
The existing binomial necessity theorem gives a>0, N=2a and N|S.
Combine j=0,N into q^N(1+c_N)/(1+q^a)². Clear every polynomial
denominator in Q[q] before evaluating at a primitive Nth root ζ.
Every remaining denominator is nonzero there, while the paired numerator is
ζ^N(1+ζ^S)=2. This contradiction rules out a squared binomial, including
N=2. No rational function is evaluated at a pole.

For rectangle existence, put η=(m^r), N=2a. Reflection of the block
polynomial and reversal of each interval 1,…,m give
c_(N−j)=q^S c_j q^(−(m+1)j), where S=a(m+1).
Define L_s=Σ_j c_j q^(−sj)/(1+q^(j−a)). Direct algebra gives
L_(s+1)+q^(−a)L_s=block(q^(−s−1)). For 1≤s+1≤m, the latter vanishes,
so L_m=(−q^(−a))^m L_0. Reflecting the finite sum gives
L_0=q^(ma)L_m. If m is odd, L_0=−L_0 and hence L_0=0.
This proves the printed root for every positive m,r with m odd and r even.
It replaces the need for general inversion symmetry and full rectangle
reciprocity in this part of the formal proof.

Integral divisibility is proved directly. For a polynomial P over an integral
coefficient ring and an injective map to a field, a zero at −u⁻¹ implies that
the polynomial reflected at its ambient degree has the integral zero −u.
The monic factor theorem gives X+u integrally. Reflecting that factorization
back gives 1+uX. This applies through the proved injective qCoeffHom and an
explicit retraction from integer polynomials in y over Z[x] to the literal
MvPolynomial ring. It supplies the printed factor in Z[x,y], not just Q(q)[y].

Removing that factor leaves no binomial divisor: a different slope contradicts
the midpoint theorem, and the same slope contradicts the new no-square theorem.
By U1 every source-general unitary divisor of the cofactor would be a
signed binomial divisor of A, contradicting this exclusion. The binomial
itself is unitary (use F=1+Y, whose only complex root is -1), so the
rectangle construction also proves the reverse implication. This gives
both directions and the printed quotient clause. ∎


A recent published route to the existence half deserves a qualification:
Ayyer–Sundaravaradan, arXiv:2606.12919v1 (2026), note a gap in the original
Carnevale–Voll Proposition 2.12 proof and provide a bijective proof of the
balanced-word reciprocity, also crediting Tielker's thesis. The direct
block-reflection argument above does not depend on that original proof.

## Significance and provenance

The exclusion of nonrectangles is the substantive new argument: the second
pole produces a centered sine sum, and strict sinc comparison makes its sign
negative for every nonconstant list of lengths. The existence half for odd
part size and even number of parts follows quickly from known reciprocity;
it is not claimed as an independent new result. Simion's root theorem,
MacMahon's formula and Han's equidistribution are published mathematics.
No claim about the stronger univariate −1 nonvanishing conjecture is made.
The first pole reductions originated in the earlier unpublished project lane
`fresh-shard053-discovery-sol61-20261119-r2`; the strict sine-sum step and this
application were developed in `t1-pool002-proof-sol61-20261120-r1`.
The sibling `t1-pool005-proof-sol61-20261120-r1` obtained an independent proof
and a route avoiding Simion. This packet follows the E2 endpoint and proves U1 by the short-arc endpoint
argument above, developed in stage 4 from that direct pole approach.

## Prior art (supplied cross-model review, dated 2026-11-20)

The following bounded audit is reproduced from the supplied Opus review.
It is not represented as a fresh independent search by this implementation lane.
Paths and first-person claims inside the reproduced audit refer to the review
lane `t1-prelean-X8-opus-20261120-r1`, not to newly performed searches here.

- Omega issues and PRs: I searched "2108.04700", "1607.01292", "Denert unitary factor", "Carnevale Voll", "Euler-Mahonian", "multiset permutations unitary" and "351584". All returned [] (`sources/omega-searches.txt`). The Sol lane's phrase search "unitary factor" returned two unrelated issues, #25007 and #27686.
- `principia-ids.txt` does not list 351584. A grep of the Principia clone for 2108.04700, Denert or Carnevale found nothing.
- Source versions: arXiv 2108.04700 has only v1. The journal (accepted 2022-06-08) keeps the conjecture. Carnevale–Voll v1–v3 and the Springer text keep it. Carnevale 2017 (EJC 24(3) P3.27) proves only the two-equal-odd-parts case.
- Citers checked by the Sol lane through OpenCitations, with bodies read:
  - Carnevale–Moustakas–Rossmann (BLMS 2025)
  - Tielker, arXiv:2203.15774
  - Rossmann (PLMS)
  - Lee–Voll
  - Abdesselam (2019). Its last section says Carnevale–Voll Conjecture A is still open.
- My own additional checks:
  - Huang–Wen–Yan, arXiv:2601.20201 (Jan 2026): new bijections for Han's equidistribution, no factorisation result.
  - Carnevale's homepage publication list (current): nothing after BLMS 2025 and no preprint on this.
  - Web searches (thesis, conjecture wording, the factor 1 + xq^{rm/2}): nothing.
- Residual: Tielker's PhD thesis. pub.uni-bielefeld.de serves an Anubis challenge, which the Sol lane and I respected. Search snippets show it discusses the conjecture. If it contained a proof, the authors' 2025 BLMS paper, which cites both source papers, would most likely say so. I put the risk at about 5%.

Nothing public resolves the conjecture, as far as an honest search reaches.


## What the Lean statement covers

`source_conjecture_351584 (H_published_CarnevaleTielker_formula10 :
SourceFormula10) : Conjecture23` quantifies over every nonempty list of
positive natural parts. Its first clause is precisely the equivalence between
a nonconstant source-unitary divisor of the literal `denertPoly` in Z[x,y]
and a list `replicate r m` with m,r positive, m odd, r even. The second
clause supplies an integral cofactor for `1+x^(eta.sum/2)*y` and says it has
no source-general unitary divisor. For a rectangle eta.sum=rm, so this is
the printed factor. One-part compositions, odd total size, and N=1,2 are
included. No bound on composition size or slope appears.

The literal objects are the multiset words, trivial word, excedances,
ordered exceeding/non-exceeding subwords, weak/strict inversion counts,
Denert's statistic, its enumerator in Z[x,y], and the nonconstant unitary
predicate with a,b in N₀. Zero exponents are permitted in the predicate;
positivity is proved for divisors, not imposed in its definition.

The single assumption is the universally quantified, literal power-series
`SourceFormula10`. Neither that formula nor its truth for all compositions
has been reclassified as kernel-proved. Small literal tests provide
transcription checks. The supplied E2 endpoint intentionally leaves the
published formula as its one external mathematical link. All proofs after
it, including the rational bridge, general unitary reduction, classification,
integral factor, multiplicity and absence of unitary factors of the cofactor,
are kernel-checked with only propext, Classical.choice, Quot.sound.

The retained Blueprint M5, R1, S2–S4 are unused, unproved proposition
specifications from the original plan. They assert no fact and are not
assumptions or dependencies of the final theorem. The retained historical
`assembly_requires_U1` helper has an explicit U1 parameter; the final theorem
supplies the proved `unitary_binomial`, so its public type has no U1 parameter.
The source appendix retains all prior modules byte-identically and places
the seven new modules after their dependencies. REPORT.md supplies the exact
statements and receipts. No independent root replay or fresh prior-art search
is claimed by this implementation lane.


## Independent final check, 2026-11-20

The final-check lane independently enumerated all 127 positive compositions
of sizes 1 through 7 (52,609 words). Literal (den,exc) and (maj,des)
enumerators agree. Direct inverse/Hadamard expansion agrees through degree
2N+2 in y; the full cleared rational identity is also checked exactly,
so this is not merely a finite series-precision comparison. Exact integer
bivariate factorisation gives only the predicted simple unitary factors,
for (1,1), (1,1,1,1), (1,1,1,1,1,1), and (3,3), with unitary-free
cofactors. This is an independent transcription check, not the universal
proof. Scripts and receipts are in `t1-final-check-351584-sol61-20261120-r1`.

Fresh omega issue and PR searches for both source arXiv identifiers and
“Carnevale Voll” returned no hits. Local Principia, mio-qwq, omega and
openai/math searches found no matching resolution. The latest source
versions and the 2026 balanced-word and multipermutation papers were
checked; no prior full classification was found. Tielker's thesis remained
access-denied and was not bypassed. Novelty remains a bounded-search
conclusion. The full final review records the sources and exact searches.
