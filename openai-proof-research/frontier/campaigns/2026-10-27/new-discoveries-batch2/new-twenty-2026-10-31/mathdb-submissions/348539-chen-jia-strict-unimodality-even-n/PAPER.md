# Strict unimodality of a Gaussian difference for even n

MathDB 348539. Chen–Jia Conjecture 3.3, with n even as in definition (3.4).
Formalization stage 3, 20 November 2026.

## Abstract

For every even n≥8 and every k≥15, the polynomial
F_{n,k}(q)=[n+k choose k]_q−q^n[n+k−2 choose k−2]_q has degree nk,
is symmetric, has equal initial coefficients f₀=f₁=1, and satisfies
f_{m−1}<f_m for 2≤m≤nk/2. We prove this using the support of the
semi-invariants modulo their invariant quadratic. Primality of that quadratic
makes nonzero support additive. The uniform degree-six seed is established
by 3,632 exact bivariate Newton certificates. Smaller residue calculations
supply central seeds in degrees three, four and five; eight finite Gaussian
calculations handle the exceptional values n=10,14. All definitions and
bridges, including Sylvester's dimension formula, are formalized in Lean.
Verification status and receipts are stated separately in REPORT.md.

## 1. The statement and its literal interpretation

The source is W. Y. C. Chen and I. D. D. Jia, *Semi-invariants of Binary Forms
Pertaining to a Unimodality Theorem of Reiner and Stanton*,
arXiv:2011.01467v2, §§1–3, International Journal of Mathematics 32(12),
2140003 (2021), DOI 10.1142/S0129167X21400036. Source files and the supplied
proof and review are identified by SHA-256 in source-binding.json.

Conjecture 3.3 states verbatim:

> For n ≥ 8 and k ≥ 15, F_{n,k}(q) is strictly unimodal, except for the two
> terms at both ends.

Definition (3.4) is

F_{n,k}(q)=[n+k choose k]_q−qⁿ[n+k−2 choose k−2]_q,

and is immediately followed by:

> where k ≥ 2 and n is even.

The source defines strict unimodality by:

> We say that f(x) is strictly unimodal if (1.6) is to be replaced by
> a₀ < a₁ < ··· < aₘ > aₘ₊₁ > ··· > aₙ. (1.7)

Its partition definition preceding (2.12) reads:

> The monomials in Q_n(k,m) are in one-to-one correspondence with partitions
> of m into k parts with zero parts allowed and each part not exceeding n.

> Let p(k,n,m) denote the number of partitions of m contained in a k × n
> rectangle, then we have

[n+k choose k]_q=Σ_{m=0}^{nk}p(k,n,m)qᵐ. (2.12)

The Lean definitions implement precisely these partitions as antitone tuples:

```lean
def box (n k : ℕ) : Finset (Fin k → Fin (n+1)) :=
  Finset.univ.filter (fun v => Antitone v)
def wt {n k : ℕ} (v : Fin k → Fin (n+1)) : ℕ := ∑ i, (v i : ℕ)
def gauss (n k : ℕ) : Polynomial ℤ := ∑ v ∈ box n k, Polynomial.X ^ wt v
def F (n k : ℕ) : Polynomial ℤ := gauss n k - Polynomial.X ^ n * gauss n (k-2)
```

The tuple/multiplicity equivalence and Gaussian product identity are proved,
not assumed. Let h_n(k,m)=[qᵐ](1−q)F_{n,k}(q). For m≥1 this is exactly
f_m−f_{m−1}, by `h_eq_diff`. The final statement is:

```lean
theorem chen_jia_conj_3_3 (n k : ℕ) (hn : 8≤n) (he : Even n) (hk : 15≤k) :
    (F n k).natDegree=n*k ∧
    (∀ j≤n*k, (F n k).coeff j=(F n k).coeff (n*k-j)) ∧
    (F n k).coeff 0=(F n k).coeff 1 ∧
    (∀ m, 2≤m → m≤n*k/2 → (F n k).coeff (m-1)<(F n k).coeff m)
```

The theorem retains the even-n domain stated immediately after (3.4) in
arXiv v2 (after (3.3) in v1), also explicit in the MathDB record. Conjecture 3.3
does not repeat that restriction, and the preceding paragraph mentions F_{5,9}.
We therefore identify the result as Conjecture 3.3 for even n, as in (3.4).
The formula itself is meaningful for odd n. If k is also odd, symmetry forces
two equal central coefficients, which violates the single-peak definition (1.7),
even after excepting the end pairs: for example, F_{9,15} has degree 135 and
f_{67}=f_{68}=17487. If n is odd and k is even, this obstruction disappears;
F_{9,16}, for example, has a strict central peak f_{72}=25113, with
f_{71}=f_{73}=25056. No assertion for that additional domain is proved here.
A reading of the printed sentence without the standing domain restriction
would thus be false, rather than a broader true conjecture fully proved by
this endpoint. Version 1 also omitted the end-pair exception in Conjecture 3.3;
version 2 explicitly includes it and is the statement addressed here.
For even n, nk/2 is integral. The proved equality at the initial
pair, strict increase through the centre, and symmetry give exactly the stated
exception at the two terms at each end. The independently proved f₀=f₁=1
also ensures positive coefficients throughout; no vacuous interpretation is used.

## 2. Literal Gaussian coefficients and Sylvester's formula

Use R=ℚ[a₀,…,a_n]. A monomial a^ν has degree Σν_i and weight Σiν_i.
The Lean subspace `piece n k m` is the span of exactly the monomials with these
two values. A monomial basis and the tuple/multiplicity bijection prove that
its dimension is [qᵐ]gauss n k. A partition recurrence proves the q-Pascal
identity; multiplying it by the denominator proves

gauss(n,k) ∏_{i=1}^k(1−qⁱ)=∏_{i=1}^k(1−q^{n+i}).

Define derivations D(a_i)=i a_{i−1} and U(a_i)=(n−i)a_{i+1}, with zero
at the respective boundary. `semi n k m` is the kernel of D on the literal
piece. On monomials the positive diagonal inner product has squared norm
∏_i ν_i! binom(n,i)^{−ν_i}. The factorial/binomial recurrence proves
⟨Df,g⟩=⟨f,Ug⟩. Derivation extensionality on the generators proves
[D,U]f=(nk−2m)f on `piece n k m`.

Consequently, below the centre,
‖Uf‖²=‖Df‖²+(nk−2m)‖f‖², so U is injective. The orthogonal
complement of the range of D is zero: its elements are killed by the adjoint
U, which is injective on the preceding weight piece. Finite dimensionality
then makes D surjective onto weight m−1 for 1≤m≤nk/2. Rank–nullity gives

 dim semi(n,k,m)=[qᵐ]gauss(n,k)−[q^{m−1}]gauss(n,k).

Weight zero is handled separately: all positive-index derivatives vanish there.
Thus `sylvester` is proved from the literal operators and inner product; it is
not an imported assertion about a different representation.

## 3. Primality, division, and additive support

Put Q=Σ_{i=0}^n(−1)ⁱ binom(n,i)a_i a_{n−i}. Direct differentiation and
(j+1)binom(n,j+1)=(n−j)binom(n,j) give DQ=0. For even n≥2, the support
consists of antidiagonal exponent pairs; distinct such monomials have disjoint
variable supports. The a₀a_n coefficient is 2, the middle-square coefficient
is nonzero, and a₀ occurs with exponent one. The formal proof uses Mathlib's
irreducibility criterion for disjoint support, then polynomial factoriality
to conclude `Q_prime`. This is the support-based proof actually formalized;
no matrix-rank theorem is assumed.

For completeness, the elementary reason for irreducibility in this situation
is as follows. A nontrivial factorization of a homogeneous quadratic over a
field would be a product L M of linear homogeneous forms. The a₀² coefficient
forces one of their a₀ coefficients to vanish, say that of L. The nonzero
a₀a_n coefficient then forces the a₀ coefficient of M and the a_n coefficient
of L to be nonzero. Every other a₀a_j coefficient is zero, forcing all other
coefficients of L to vanish. Thus L is a multiple of a_n, contradicting the
nonzero a_{n/2}² coefficient. The disjoint-support criterion used in Lean
packages this irreducibility argument for the actual antidiagonal support.

If Df=0 and f=Qg, differentiation gives Q Dg=0, hence Dg=0. The two
Euler derivations for degree and weight characterize the literal pieces.
Applying them to f=Qg and cancelling Q shows that g has degree k−2 and
weight m−n when k≥2 and m≥n. For m<n, the corresponding weight of g
would be negative; its coefficients therefore vanish, so nonzero f of that
weight cannot be divisible by Q.

Let `NonzeroClass n k m` mean that there is a semi-invariant in that piece
which is not divisible by Q. This realizes nonzero support of A/QA, where
A=ker D. The cancellation statement gives A∩QR=QA, so A/QA embeds in
R/QR. Since Q is prime, products of representatives not divisible by Q remain
not divisible by Q. Lean proves this directly in `nonzeroClass_add`; it need
not construct an abstract quotient algebra to use its domain property.

Multiplication by Q is an injective linear map from semi(n,k−2,m−n)
onto the divisible semi-invariants in semi(n,k,m). Its rank, Sylvester's
formula, and the low-weight argument prove the exact bridge

 NonzeroClass(n,k,m) ↔ 0<h_n(k,m),  for k≥2 and 2m≤nk.

The degree-one class a₀ is nonzero, so any such class can be padded to a larger
degree without changing its weight. These are the only propagation principles
used below.

## 4. Rational series and exact residue certificates

Putting the proved Gaussian products over a common denominator yields

 (1−q)F_{n,k}(q)=
 (1−qⁿ)(1−q^{n+2k−1}) ∏_{i=1}^{k−2}(1−q^{n+i}) /
 ∏_{i=2}^k(1−qⁱ).                                               (A)

All cancellation is performed as a polynomial identity before passing to
formal power series. For positive integers d, `coinFactor d` has coefficient
1 at multiples of d and 0 elsewhere, and satisfies
coinFactor(d)(1−qᵈ)=1. Their product `coinSeries S` therefore has precisely
the restricted-partition coefficients P_S(v), taken to be zero for v<0.

If every d∈S divides L, let d₀=|S| and
C_S(q)=∏_{d∈S}(1+qᵈ+⋯+q^{L−d}). Then
coinSeries(S)=C_S(q)/(1−qᴸ)^{d₀}. For 0≤r<L, numerator support gives

 P_S(Lz+r)=Σ_{j=0}^{d₀−1}[q^{Lj+r}]C_S(q)
             binom(z+d₀−1−j,d₀−1).                            (B)

This is a proved polynomial identity in every natural z, not interpolation
from samples. The right side defines the extension at negative arguments.
For S={2,3,4,5,6}, deg C_S=280, and the residue-polynomial extension of P_S
is zero at −19,…,−1. The analogous
boundaries for {2,3}, {2,3,4}, {2,3,4,5} are −4,…,−1, −8,…,−1, and
−13,…,−1. The finite numerator lists, their products, their support bounds,
and these boundary values are all kernel checked.

For k=6, expanding the actual six numerator factors of (A), and using m≤3n,
removes all triples and higher products. With I={0,1,2,3,4,11}, this gives

 h_n(6,m)=P(m)−Σ_{i∈I}P(m−n−i)+Σ_{i<j}P(m−2n−i−j).

For m<n it reduces to P(m)>0 for m≥2, since every such m is 2a+3b.
The formal proof establishes coefficient nonnegativity and convolution
positivity for the genuine coin series, then uses this representation.
For n≤m≤2n put x=m−n,y=2n−m; for 2n≤m≤3n put
x=m−2n,y=3n−m. In both cases x,y≥0 and n=x+y. The resulting expressions are

 H₁(x,y)=P(2x+y)−Σ_{i∈I}P(x−i),
 H₂(x,y)=P(3x+2y)−Σ_{i∈I}P(2x+y−i)+Σ_{i<j}P(x−i−j).

All retained negative arguments are within the proved boundary. Write
x=60(b_x+u)+r,y=60(b_y+v)+s with r,s<60. Evenness requires r+s even.
If r+s≥8 take b_x=b_y=0. If r+s<8, n≥8 forces at least one positive
quotient; use bases (1,0) or (0,1). There are 1,816 cases per region,
hence 3,632 cases in total. `residue_cover` proves exhaustiveness.

Each case is a rational polynomial of total degree at most four. The shared
table contains the five integer coefficients of 24 times each of the 60
residue quartics. A finite kernel decision checks the table against (B),
and a general ring identity proves its evaluation formula. Each case stores
15 exact integer Newton coefficients and proves, by `ring`, the identity

 H_e(...)=Σ_{i+j≤4} c_{ij} binom(u,i)binom(v,j).

The kernel also checks c₀₀>0 and all other c_{ij}≥0. The proved Newton
soundness lemma uses nonnegativity of natural binomial coefficients, giving
strict positivity for every natural u,v. Python merely proposes integer
coefficients: its dynamic programming and finite differences are not trusted.
The Lean identities independently verify them. There are 364 data modules: 363 contain ten cases each and the last contains
two. This keeps checks small. Each includes a literal h positivity consequence; row lemmas and
`all_cases_positive` assemble the complete finite coverage. `L6` is therefore
uniform for every even n≥8 and 2≤m≤3n.

## 5. Central seeds and exceptional finite seeds

The same numerator/series method for the smaller coin sets proves:

* L3: h_n(3,3n/2)=1 when 4 divides n and n≥8.
* L4: h_n(4,2n)=⌊n/6⌋ when n is even and n≥8.
* L5: h_n(5,5n/2)>0 when n≡2 mod 4 and n≥18.

For L3 write n=4t and t=3u+r with r∈{2,3,4}; three linear residue
identities give 1. The formal numerator route is
P_{2,3}(6t)−P_{2,3}(2t)−P_{2,3}(2t−1)−P_{2,3}(2t−5),
which follows directly from (A).
For L4 write n=12u+r with r∈{8,10,12,14,16,18}. Six quadratic
identities give 2u+⌊r/6⌋. For L5 write n=4t+2, t=30u+r with
4≤r≤33. Thirty cubic Newton identities have positive constants and
nonnegative remaining coefficients. All these are exact polynomial identities
using (B), with the negative boundaries already justified.

For n=10,14 and k=15,16,17,18, literal Gaussian lists are generated by
gauss(n+1,k+1)=gauss(n,k+1)+q^{n+1}gauss(n+1,k), starting at the
constant boundary. Each list equality is checked with ordinary kernel decision;
a single proved polynomial-list recurrence transfers it to `gauss`.
The eight h positivity lemmas then check all 784 required adjacent differences.
No supplied finite polynomial is identified with `gauss` merely by its name.

## 6. Covering and the exceptional induction

Call degree c support central when its weight is c(n/2). Products of central
classes remain central. If 4 divides n, degrees 3 and 4 generate all central
degrees c≥6. If n≡2 mod 4 and n≥18, degrees 4,5,6 generate all central
degrees c≥8. The elementary semigroup tail lemmas are proved by induction.
Thus, in either case, every c≥8 is central, as are c=0,4.

Multiplying the degree-six class of weight u by a central degree-c class,
and then padding by a₀, gives positivity at degree k on the whole interval

 c n/2+2 ≤ m ≤ c n/2+3n,  provided c≤k−6.

Here is the covering construction actually formalized. Write a=n/2≥4.
For m≤6a use c=0. For 6a<m≤10a use c=4. For m>10a take
c=min(k−6,⌊(m−2)/a⌋), which is at least 8 because k−6≥9.
The quotient/remainder inequalities give ca+2≤m. If c=k−6 the upper
bound m≤ka is exactly m≤ca+6a; otherwise the remainder bound gives
m<ca+a+2≤ca+6a. This proves `interval_cover` without an implicit
assumption about consecutive semigroup elements. The support bridge then
proves every required strict step for n other than 10,14.

For n=10,14, use strong induction on k≥15. The eight checked seeds cover
15≤k≤18. If k≥19 and m≤n(k−1)/2, the induction hypothesis at degree
k−1 and padding prove the claim. Otherwise multiply the central degree-four
class by the induction class at degree k−4 and weight m−2n. The centre
bound gives m−2n≤n(k−4)/2. Since k−1≥18 and m>n(k−1)/2, one
also has m−2n≥2. Thus the induction hypothesis applies. `exceptional_induction`
formalizes this argument uniformly, and `exceptional_strict` supplies the
literal n=10,14 seeds. The two cases exhaust every even n≥8. Degree,
symmetry and the end pair complete `chen_jia_conj_3_3`.

## 7. Significance, attribution, and verification

The additional ingredient beyond weak unimodality is the use of nonzero support
in the quotient by Q. The domain property makes that support additive; it does
not justify subtracting two arbitrary positive dimensions. The formal quotient
dimension bridge and the uniform certificates are essential. The certificates
prove unbounded residue families, not a bounded scan. Their size makes this a
computer-assisted proof; it is not presented as a short conceptual replacement
for the source's invariant theory.

The supplied Opus review found no proof or disproof of Conjecture 3.3 in the
public sources it checked. It found the source's later semi-invariant/additivity
paper, Ji's q-Kaplansky work, Koutschan–Uncu–Wong's related weak-difference
results, and Prellberg's related comparisons, without a proof of this strict
r=2 result. That review is a bounded prior-art search, not a claim of exhaustive
novelty. Credit for the semi-invariant interpretation and additivity methods
belongs to Chen–Jia and their cited predecessors; the quasipolynomial
certificate approach is related to Koutschan–Uncu–Wong. The quotient-domain
propagation plus the explicit uniform seeds are the new combination used here.
No fresh publication or submission is part of this packet.

The complete Lean sources, including all data, appear byte-for-byte in
LEAN-SOURCE-APPENDIX.md in import order. REPORT.md and verification-inventory.json
record compilation, separate standalone kernel checks, hashes, and any remaining
obligations. Only propext, Classical.choice, and Quot.sound are permitted;
ENDPOINT-AXIOMS.txt records the actual axiom printout. Every Lean invocation uses
the copied unchanged runner and pinned toolchain. No native evaluation oracle,
unproved declaration, changed runner limit, or paper-only model bridge is used.

### Verbatim prior-art record from the supplied review

> - Principia id list and the Principia clone: no hit for 348539 or for 2011.01467.
> - Omega registry, searched separately from the earlier Sol lanes: `gh search issues` and `gh search prs` for "2011.01467" returned `[]`. "Reiner Stanton" returned one issue and one PR, both about Okada's pre-merged determinants (#25498, #25571), so unrelated. "Chen Jia semi-invariants", "strictly unimodal Gaussian" and "348539" returned `[]`.
> - arXiv history: v1 (Nov 2020), v2 (14 Sep 2021). Journal version: IJM 32(12) 2140003 (2021). v2 still prints Conjecture 3.3 verbatim.
> - Citing works, from my own Semantic Scholar query (`logs/s2-348539-cites.json`): Chen–Jia, *Semi-invariants of binary forms and Sylvester's theorem* (arXiv:2011.03458, Ramanujan J.); Chen–Jia, the *additivity lemma of Pak and Panova* version of that paper; Ji, q-Kaplansky (2111.03369); Koutschan–Uncu–Wong (2302.04067, ISSAC 2023); Prellberg, *A positivity conjecture of Prellberg and Stanton* (2610.26878, Oct 2026). OpenAlex reports 3 citations; its daily budget then ran out and I did not work around that. I read the Prellberg paper's introduction, the place where it cites Chen–Jia, and its open problems: it cites [6,7] only as "related comparisons" and does not touch F_{n,k}. The Sol lanes had already read the theorem statements of Ji and KUW: weak results only, for fixed small k.
> - Three web searches (extended and standard): no proof or refutation of Conjecture 3.3 anywhere, and no strict-unimodality result for r=2.

