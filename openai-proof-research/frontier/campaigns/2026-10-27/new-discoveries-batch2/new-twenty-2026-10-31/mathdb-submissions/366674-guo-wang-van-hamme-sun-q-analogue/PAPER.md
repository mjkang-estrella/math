# A proof of Guo–Wang Conjecture 4.1, with a Lean certificate

**Status.** The conjecture is proved for every positive n ≡ 1 (mod 4), composite n included, in writing (§§1–5) and in Lean 4 with Mathlib. The Lean theorem `GuoWang.guo_wang_conj_4_1` is the endpoint fixed by the independent review, unchanged, with no hypotheses beyond 0 < n and n % 4 = 1. Its axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. MathDB record 366674.

## Source statement

Guo and Wang, *Refinements of Van Hamme's (E.2) and (F.2) supercongruences and two supercongruences by Swisher*, arXiv:2501.09626v1 (16 January 2025), §4, p. 13; journal version J. Math. Anal. Appl. 551(1) (2025) 129673, DOI 10.1016/j.jmaa.2025.129673. The source definitions, verbatim (typography normalised from the PDF text extraction):

> Let [n] = (1 − qⁿ)/(1 − q) be the q-integer, (x; q)ₙ = (1 − x)(1 − xq) ··· (1 − xqⁿ⁻¹) (n ⩾ 0) the q-shifted factorial, and let the n-th cyclotomic polynomials be given by Φₙ(q) = ∏_{1⩽k⩽n, gcd(k,n)=1} (q − ζᵏ), where ζ is an n-th primitive root of unity. We believe that the following q-analogue of (4.2) should be true.

> **Conjecture 4.1.** Let n ≡ 1 (mod 4) be a positive integer. Then
> \[
>  \sum_{k=0}^{n-1}(-1)^k[6k+1]\frac{(q;q^2)_k^3}{(q^4;q^4)_k^3}q^{3k^2}
>  \equiv
>  \sum_{k=0}^{n-1}(-1)^k[8k+1]\frac{(q;q^4)_k^3}{(q^4;q^4)_k^3}q^{2k^2+k}
>  \pmod{[n]\Phi_n(q)^3}. \tag{4.3}
> \]

A congruence between rational functions of q is read in the standard way: the modulus divides the numerator of the reduced difference. (The source does not restate this convention; it is the one used throughout this literature, stated explicitly for example by Karmakar–Jana, arXiv:2610.11786, §1: "if the numerator of the reduced form of A(q) − B(q) is divisible by M(q) in the polynomial ring Z[q]". Since the modulus is monic with integer coefficients, divisibility in ℚ[q], as in the Lean statement, is equivalent to divisibility in Z[q] by Gauss's lemma.) The reduced reading is essential for composite n: for d | n with 1 < d < n, the individual summands with k ≥ d have Φ_d in their denominators, and only the reduced total is free of it. For example, for n = 9 the common denominator (q⁴;q⁴)₈³ has Φ₃-order 6 while the cleared numerator has Φ₃-order 7. Since [n] = ∏_{d|n, d>1} Φ_d(q), the modulus is Φ_n(q)⁴ · ∏_{d|n, 1<d<n} Φ_d(q).

## Lean definitions, next to the source

All objects live in `RatFunc ℚ`, with q = `RatFunc.X`. These are the definitions of `GWStatement.lean`, copied literally; the review's required block is restated character for character in `GWReviewEndpoint.lean` and proved there from the same proof (its `diff` is definitionally the lane's `diff`, checked by `rfl`).

| Source | Lean |
|---|---|
| q | `X' : RatFunc ℚ := RatFunc.X` |
| (x; b)ₖ = (1 − x)(1 − xb)···(1 − xbᵏ⁻¹) | `poch z b k := ∏ j ∈ Finset.range k, (1 - z * b ^ j)` |
| [m] = (1 − qᵐ)/(1 − q) | `qIntPoly m := ∑ j ∈ Finset.range m, X ^ j` (in ℚ[X]); `qInt m := algebraMap _ _ (qIntPoly m)`; `qInt_source` proves `qInt m = (1-X'^m)/(1-X')` with `1-X' ≠ 0` |
| Φₙ(q) | `Polynomial.cyclotomic n ℚ` (Mathlib's monic cyclotomic polynomial, whose roots are the primitive n-th roots of unity) |
| left summand | `L k := (-1)^k * qInt (6*k+1) * poch X' (X'^2) k ^ 3 / poch (X'^4) (X'^4) k ^ 3 * X'^(3*k^2)` |
| right summand | `R k := (-1)^k * qInt (8*k+1) * poch X' (X'^4) k ^ 3 / poch (X'^4) (X'^4) k ^ 3 * X'^(2*k^2+k)` |
| difference of the two sums over k = 0,…,n−1 | `diff n := (∑ k ∈ Finset.range n, L k) - (∑ k ∈ Finset.range n, R k)` |
| "≡ (mod [n]Φₙ³)" | `qIntPoly n * cyclotomic n ℚ ^ 3 ∣ (diff n).num` (`RatFunc.num` is the numerator of the reduced fraction) |

```lean
theorem GuoWang.guo_wang_conj_4_1 (n : ℕ) (hn : 0 < n) (h4 : n % 4 = 1) :
    GuoWang.qIntPoly n * (Polynomial.cyclotomic n ℚ)^3 ∣ (GuoWang.diff n).num
```

**Division by zero.** Lean sets x/0 = 0. The only division in the statement is by `poch (X'^4) (X'^4) k ^ 3`, and `poch_den_ne_zero : ∀ k, poch (X'^4) (X'^4) k ≠ 0` and `term_den_ne_zero` (its cube) are proved; [m] is a polynomial sum with no division. So no source term is silently replaced by 0.

**Non-vacuity.** `RatFunc.num 0 = 0` is divisible by everything, so we also prove `diff_five_ne_zero : diff 5 ≠ 0` and `diff_five_num_ne_zero : (diff 5).num ≠ 0` (by exact evaluation of an explicit cleared numerator at q = 2). The independent review's exact computation found the Φₙ-order of the difference to be exactly 4 for n = 5, 9, 13, 17, 21, 25, 29, 33, 37, 45 and 49. The final check recomputed n = 5, 9, 13, 17, 21 and 25 independently with the same result, and found order exactly 1 at every proper divisor Φ_d. So the Φₙ part of the modulus is sharp there and cannot be raised to Φₙ⁵, and the statement is not trivially satisfied. For n ≡ 3 (mod 4) (n = 3, 7, 15) the Φₙ-order is only 1, so the hypothesis on n is needed.

# Proof

## 1. Two finite sums with an auxiliary parameter

Work first with independent indeterminates `q,a`. Set

\[
 A_k(q,a)=(-1)^k[6k+1]q^{3k^2}
 \frac{(aq;q^2)_k(q/a;q^2)_k(q;q^2)_k}
 {(aq^4;q^4)_k(q^4/a;q^4)_k(q^4;q^4)_k},
\]
\[
 B_k(q,a)=(-1)^k[8k+1]q^{2k^2+k}
 \frac{(aq;q^4)_k(q/a;q^4)_k(q;q^4)_k}
 {(aq^4;q^4)_k(q^4/a;q^4)_k(q^4;q^4)_k}.
\]

Write `S_A(N)=∑_{k<N}A_k`, `S_B(N)=∑_{k<N}B_k`, and `D_N=S_A(N)-S_B(N)`, retaining `(q,a)` when needed. Both sums are invariant under `a↦a⁻¹`.

Put `C=(1-aq⁴)(1-a²q⁴)`. Define

\[
 g_A(x)=-C\frac{(1-x^2)(1-x^2/a)}
 {(1-qx^3)(aq^3-x)(aq-x)},
\]
\[
 g_B(y)=C\frac{(1-y)(1-y/a)}
 {(1-qy^2)(aq^3-y)(1-aq)},
\]

and `G_A(k)=A_k g_A(q^{2k})`, `G_B(k)=B_k g_B(q^{4k})`. These are rational functions, so removable expressions are interpreted by cancellation.

The exact finite WZ identities are

\[
 (1-a^{-1})A_k(q,aq^4)-(1-aq^4)A_k(q,a)
   =G_A(k+1)-G_A(k),                                      \tag{1A}
\]
\[
 (1-a^{-1})B_k(q,aq^4)-(1-aq^4)B_k(q,a)
   =G_B(k+1)-G_B(k).                                      \tag{1B}
\]

### Explicit algebra verifying the certificates

For (1A), set `x=q^{2k}` and

\[
 U_A=(1-aqx)(1-aq^3x)(1-x^2/a)
       -(aq^3-x)(aq-x)(1-aq^4x^2).
\]

For generic independent q,a, dividing by the nonzero generic `A_k` and clearing denominators reduces (1A) to the identity

\[
 -\frac{x^3}{a}(1-aqx)(1-qx)(aq^3-x)(-C)
 -(1-x^2)(1-x^2/a)(1-aq^4x^2)(-C)
 =(1-aq^4)U_A(1-qx^3).                                  \tag{2A}
\]

For (1B), set `y=q^{4k}` and

\[
 U_B=-(1-aq^3)(1-aqy)(1-y/a)
       -(1-aq)(aq^3-y)(1-aq^4y).
\]

The corresponding cleared identity is

\[
 -\frac{y}{a}(1-aqy)(1-qy)(aq^3-y)C
 -(1-y)(1-y/a)(1-aq^4y)C
 =(1-aq^4)U_B(1-qy^2).                                  \tag{2B}
\]

Multiplication by `a` makes these ordinary polynomial identities; expansion proves both. For completeness, the ratios needed to obtain them are

\[
 \frac{A_{k+1}}{A_k}=-q^3x^3\frac{1-q^7x^3}{1-qx^3}
 \frac{(1-aqx)(1-qx/a)(1-qx)}
 {(1-aq^4x^2)(1-q^4x^2/a)(1-q^4x^2)},
\]
\[
 \frac{B_{k+1}}{B_k}=-q^3y\frac{1-q^9y^2}{1-qy^2}
 \frac{(1-aqy)(1-qy/a)(1-qy)}
 {(1-aq^4y)(1-q^4y/a)(1-q^4y)}.
\]

Thus this proof does not assume either infinite summation formula or a published supercongruence.

Since `G_A(0)=G_B(0)=0`, summation gives

\[
 (1-a^{-1})D_N(q,aq^4)-(1-aq^4)D_N(q,a)
       =G_A(N)-G_B(N).                                  \tag{3}
\]

## 2. Algebraic parameter-shift obstruction

Let K be a field, u ≠ 0, and F(a)=P(a)/H(a), with P,H ∈ K[a]
and H ≠ 0. If

\[
 (1-a^{-1})F(ua)=(1-ua)F(a),
\]

then P=0. Indeed, clearing denominators gives

\[
 (a-1)P(ua)H(a)=a(1-ua)P(a)H(ua).
\]

If P ≠ 0, write v_P,v_H for the least nonzero exponents of P,H.
Rescaling by u preserves each least exponent. The two sides therefore have
least exponents v_P+v_H and 1+v_P+v_H respectively, a contradiction. This
argument also permits poles of F at a=0: clearing denominators accounts for them.

Apply the same argument coefficientwise after q is specialized to a primitive
root ζ, taking u=ζ⁴. Explicitly, suppose a cleared parameter-shift operator
is divisible by Φ_d(q). Its reduction in K[a] is the displayed homogeneous
identity, so the numerator itself reduces to zero. Rational irreducibility of
Φ_d then makes every a-coefficient divisible by Φ_d. If the operator has
Φ_d², divide that scalar factor out of the numerator and apply the argument
again. The operator commutes with multiplication by Φ_d, since Φ_d depends
only on q. Thus a double zero of the operator gives coefficientwise Φ_d²
for the numerator. Only nonzero polynomial denominators are cancelled here.

## 3. Matching the boundary terms to second order

Now let `n>1`, `n≡1 (mod 4)`, and let `ζ` be any primitive `n`th root. The summands defining `D_n` are regular at `q=ζ` over `ℂ(a)`: the unparametrized denominator factors have exponents `4j`, `1≤j<n`, and none vanishes.

Cancel the factors in the certificates to write

\[
 G_A(n)=\frac{(-1)^{n+1}Cq^{3n^2}
 (aq;q^2)_n(q/a;q^2)_n(q;q^2)_n}
 {(1-q)(aq^4;q^4)_n(q^4/a;q^4)_{n-1}(q^4;q^4)_{n-1}
 (aq^3-q^{2n})(aq-q^{2n})},                              \tag{5A}
\]
\[
 G_B(n)=\frac{(-1)^nCq^{2n^2+n}
 (aq;q^4)_n(q/a;q^4)_n(q;q^4)_n}
 {(1-q)(aq^4;q^4)_n(q^4/a;q^4)_{n-1}(q^4;q^4)_{n-1}
 (aq^3-q^{4n})(1-aq)}.                                 \tag{5B}
\]

All denominators in (5A)–(5B) are nonzero rational functions of `a` at `q=ζ`. Each numerator has the factor `1-q^n`. In `(q;q²)_n` its unique vanishing factor is indexed by `j=(n-1)/2`; in `(q;q⁴)_n` it is indexed by `j=(n-1)/4`. The latter index is the reason for `n≡1 (mod 4)`.

After division by `1-q^n`, the two unparametrized products have the same value at `ζ`: deleting the unique zero factor in each leaves exactly the product of `1-ζ^r` over nonzero residues `r mod n`. Likewise,

\[
 (a\zeta;\zeta^2)_n=(a\zeta;\zeta^4)_n=1-a^n,
\]

and the two analogous products with `a⁻¹` both equal `1-a⁻ⁿ`. The powers of `q` in (5A)–(5B) both become `1`. The last denominator factors in (5A) become `(aζ³-1)(aζ-1)`, whereas those in (5B) become `(aζ³-1)(1-aζ)`, their negative. This sign exactly compensates the opposite overall signs `(-1)^{n+1}` and `(-1)^n`. Hence

\[
 \left.\frac{G_A(n)}{1-q^n}\right|_{q=\zeta}
 =\left.\frac{G_B(n)}{1-q^n}\right|_{q=\zeta}.
\]

It follows that `G_A(n)-G_B(n)` has a double zero at `q=ζ`. Apply the algebraic parameter-shift obstruction twice to the cleared form of (3):

\[
                 D_n(q,a)\equiv0\pmod{\Phi_n(q)^2}.       \tag{6}
\]

Here and below a statement with indeterminate `a` is a rational-function statement, not an assertion at exceptional parameter poles. Clearing the explicit common denominators shows that (6) holds coefficientwise in `a`.

## 4. Two terminating parameter zeros supply two more factors

Write `n=4m+1`. For `a=q^{4j+1}`, `0≤j≤m-1`, the products `(q/a;q²)_n` and `(q/a;q⁴)_n` both vanish identically: their zero factors have indices `2j` and `j`, respectively. Use the cancelled boundary forms (5A)–(5B), whose denominators are nonzero at these parameters: the possible monomial equalities would require 4j+2 or 4j+4 to equal 2n or 4n, while 4j+4<n. Thus `G_A(n)=G_B(n)=0` there. The raw certificates inside the telescoping sum can have removable poles; they are never specialized term by term. Equation (3) yields

\[
 (1-q^{-(4j+1)})D_n(q,q^{4j+5})
 =(1-q^{4j+5})D_n(q,q^{4j+1}).                           \tag{7}
\]

At `a=q`, all positive-index summands in both sums vanish, so `D_n(q,q)=0`. Induction using (7) proves `D_n(q,q^n)=0`. Symmetry in `a,a⁻¹` proves `D_n(q,q^{-n})=0`.

Choose a polynomial numerator `P(q,a)` for `D_n(q,a)` by clearing the displayed finite-product denominators and powers of `a`. The two applications of the obstruction prove directly that `Φ_n(q)²` divides every a-coefficient of this polynomial in ℚ[q]. Thus write `P=Φ_n² H`, with `H` a polynomial in `q,a`.

Work now over the domain `R=ℚ[q,q⁻¹]`, viewing `H` as a polynomial in `a`. The original common denominator is not identically zero when `a=q^n` or `a=q⁻ⁿ`: its parameter exponents are multiples of four, whereas n is odd. The terminating zeros therefore imply `P(q,q^n)=P(q,q⁻ⁿ)=0`. Since `Φ_n²` is a nonzero element of the domain R, they also imply `H(q,q^n)=H(q,q⁻ⁿ)=0`.

The two elements `q^n` and `q⁻ⁿ` of R are distinct because n>0. Apply monic polynomial division successively: first `H=(a-q^n)H₁`; evaluating at `q⁻ⁿ` gives `(q⁻ⁿ-q^n)H₁(q,q⁻ⁿ)=0`, hence `H₁(q,q⁻ⁿ)=0` in the domain; therefore `H₁=(a-q⁻ⁿ)H₂`. No comaximality of these two root ideals is assumed. Consequently

\[
 P=\Phi_n(q)^2(a-q^n)(a-q^{-n})H_2\quad\text{in }R[a].
\]

Setting `a=1` and using `1-q⁻ⁿ=-q⁻ⁿ(1-q^n)` shows that `P(q,1)` is divisible, up to a Laurent monomial unit, by

\[
                  \Phi_n(q)^2(1-q^n)^2,
\]

hence by `Φ_n(q)⁴`. Specialization has not introduced a denominator zero at a primitive `n`th root: all remaining denominator factors are powers of `1-q^{4j}`, `1≤j<n`, and monomials. Therefore

\[
                 D_n(q,1)\equiv0\pmod{\Phi_n(q)^4}.       \tag{8}
\]

This Laurent-ring argument cannot lose a cyclotomic factor: its only additional units are nonzero constants and powers of q. Equivalently, clearing the Laurent monomial yields the same ordinary-polynomial divisibility because q is relatively prime to `Φ_n` for n>1.

## 5. The proper divisors of n

It remains to establish the factor `[n]/Φ_n`, without importing a supercongruence from the literature.

First, for **every odd `d>1`**, not only `d≡1 (mod 4)`, both `S_A(d;q,a)` and `S_B(d;q,a)` vanish at a primitive `d`th root `ζ`. Indeed, the individual recurrences obtained from (1A) and (1B) have boundary terms (5A) and (5B), with `n` replaced by `d`. Each boundary has a zero from its unparametrized numerator. The denominator is regular over `ℂ(a)`. In `(q;q⁴)_d` the zero is `1-q^{sd}`, where `s=1` if `d≡1 (mod 4)` and `s=3` if `d≡3 (mod 4)`. The algebraic parameter-shift obstruction applies once to each sum separately. Specializing `a=1` is legitimate for length `d`, so

\[
                      S_A(d;\zeta,1)=S_B(d;\zeta,1)=0.    \tag{9}
\]

We spell out the block calculation extending (9) to a multiple `n=td`. For `ℓ≥0`, `0≤r<d`, define

\[
 c_A(\ell)=\prod_{j=0}^{\ell-1}\frac{2j+1}{4j+4},\qquad
 c_B(\ell)=\prod_{j=0}^{\ell-1}\frac{4j+s}{4j+4}.
\]

Cancellation of the zero factors in each complete block of `d` factors gives

\[
 \left.\frac{(q;q^2)_{\ell d+r}}{(q^4;q^4)_{\ell d+r}}\right|_{q=\zeta}
       =c_A(\ell)\left.\frac{(q;q^2)_r}{(q^4;q^4)_r}\right|_{q=\zeta},
\]

and the analogous identity with `(q;q⁴)` and `c_B`. To verify this directly, each complete block's nonzero factors run through all nonzero residues and cancel. The ratios of the zero factors are `(2j+1)/(4j+4)` or `(4j+s)/(4j+4)`, because `(1-q^{ud})/(1-q^{vd})` tends to `u/v` at `ζ`. A residual numerator zero simply makes both sides zero; there is no residual denominator zero for `r<d`. In particular every term is regular at `ζ`.

The powers of `ζ` and the q-integer factors of a summand depend only on `r`, whereas `(-1)^{ℓd+r}=(-1)^ℓ(-1)^r`. Consequently

\[
 A_{\ell d+r}(\zeta,1)=(-1)^\ell c_A(\ell)^3 A_r(\zeta,1),\qquad
 B_{\ell d+r}(\zeta,1)=(-1)^\ell c_B(\ell)^3 B_r(\zeta,1).
\]

Summing over the `t` complete blocks and using (9) proves that both length-`n` sums vanish at `ζ`. This holds for every `d>1` dividing odd `n`. Their difference is regular at all these roots and has numerator divisible by

\[
                         [n]=\prod_{d\mid n,\ d>1}\Phi_d(q). \tag{10}
\]

Combining (8) and (10), by pairwise coprimality of the cyclotomic polynomials, yields exactly divisibility by `[n]Φ_n³`. For `n=1`, both original sums consist of the term `1`, so their difference is zero. This completes the proof. ∎


## How the Lean proof follows the written proof

The development has 66 modules (about 4,450 lines). All proofs are finite polynomial algebra; no published supercongruence, summation formula or theorem outside Mathlib is assumed.

- **Bridge to polynomials** (`GWRatBridge`, `GWClearProducts`, `GWClearSums`, `GWClearSpecialize`). The parametric difference D_N(q,a) is written as P/H with explicit P, H ∈ ℚ[q][a] (numerators and denominators multiplied by aᵏ). Every specialisation (a ↦ aq⁴, q^{4j+1}, q^{±n}, 1, and q ↦ ζ) is a ring homomorphism applied to this identity, and each use is preceded by a proof that the specialised denominator is nonzero. `diff_fraction` proves `diff N = P(q,1)/H(q,1)`, and `modulus_dvd_reduced_num_iff` transfers divisibility to the reduced numerator `(diff n).num` using coprimality of Φₙ with H(q,1).
- **Certificates and telescoping** (`QWZCore`, `GWRationalA/B`, `GWTelescope`, `GWField*`, `GWPolynomialRecurrence`): identities (1A), (1B), (3), descended to the polynomial identity `polynomial_recurrence` with cancelled boundary terms.
- **Boundary matching** (`GWBoundary*`, `GWResidueProducts`, `GWDeletedBoundary`, `GWCancelledBoundary`): (5A), (5B), the residue-product bijections and the first-order matching at ζ.
- **Parameter-shift obstruction** (`GWShiftObstruction`, `GWOperator*`, `QCyclic`): the least-exponent argument of §2, applied twice (`actual_operator_sq`) to get Φₙ² coefficientwise.
- **Terminating zeros** (`GWTerminating*`, `GWInverseRoot`): `at_P_qn`, `at_P_qn_inverse`, by induction from a = q.
- **Fourth power** (`GWExtractFourth`, `GWTopFourth`): `top_fourth : cyclotomic n ℚ ^ 4 ∣ (diff n).num`. The Laurent division of §4 is replaced by multiplying the inverse-root evaluation by a power of q, so only ordinary polynomials occur.
- **Proper divisors** (`GWValues`, `GWBlock*`, `GWFamily*`, `GWLongRatio`, `GWProperDivisors`): `proper_cyclotomic`, via certified polynomial-fraction representatives (`HasValue`) for the block cancellation of §5.
- **Assembly** (`GWAssemble`, `GWConjecture`): coprimality of distinct cyclotomic factors gives the full modulus; n = 1 is `diff 1 = 0`.

## Significance

This settles a conjecture that its authors, who include a co-inventor of the creative-microscoping method, described as "still rather challenging". The published results closest to it give the congruence modulo [n]Φₙ(q)², one power of Φₙ short (Guo–Zudilin, for each side separately). For the right-hand (8k+1) side alone, Wang–Tian–Huang (arXiv:2505.04395, with a source author as first author) go to modulus [n]Φₙ(q)³ with an explicit correction term, but they say nothing about the bibasic left-hand side and do not claim Conjecture 4.1. The proof uses standard tools (q-Gosper certificates, creative microscoping, products over roots of unity). What is new is the observation that the two families satisfy the *same* inhomogeneous a → aq⁴ recurrence, and that their boundary terms agree to first order at primitive n-th roots. Cyclic annihilation then gives the parametric difference to order Φₙ² before the terminating parameter zeros add two more factors. The argument is short, about two pages. The independent review judged it borderline on whether a specialist would call it routine (probability 0.55 that it is not routine), and we do not claim more: a referee in this area could reasonably regard it as a nice application of known methods rather than a new technique. The formal certificate removes doubt about correctness, including the many specialisation and denominator conditions the written argument handles informally, but it says nothing about novelty or importance. The source authors had already proved the integer analogue (4.2) modulo p⁴ for primes p; the new content is the q-analogue (4.3), and, relative to published results, literally the fourth power of Φₙ.

## Prior art (independent review, 2026-11-20, refreshed by the final check the same day)

**Shortest published route.** Guo–Zudilin give each side ≡ (−q)^{(n−1)(n−3)/8}[n] modulo [n]Φ_n², which leaves the difference one power short. Wang–Tian–Huang give the right side to fourth order. A matching fourth-order evaluation of the *left* (bibasic) side would finish it. I found none published, and the proof lane's jet computation reports that the left side's tail is generally nonzero at cubic order, so the right side's method does not transfer verbatim. **No short route from published theorems.**

The review's bounded search: arXiv:2501.09626 has only v1, and both its abstract and the journal abstract still announce the conjecture as open; the journal's subscription body was not read. Semantic Scholar lists three citing works (Wang–Tian–Huang, arXiv:2505.04395, which treats the right-hand (8k+1) family modulo [n]Φₙ³ and does not claim Conjecture 4.1; Valloud, arXiv:2508.00343, ordinary WZ; Wei–Yu, BMMSS 2026, a different series). OpenAlex counts four, and the fourth is unidentified. Mu–Zhong, arXiv:2611.20776 (16 Nov 2026), treats n ≡ 3 (mod 4) and a different family. Omega and Principia registry searches found nothing. The review put the residual risk that a published proof exists at about 8%.

**Final-check refresh (2026-11-20).** OpenAlex now lists all four citing works of the journal version. The fourth, previously unidentified, is W.-W. Qi, *A q-supercongruence arising from Lehmer–Euler numbers*, J. Inequal. Spec. Funct. (2025) (arXiv:2507.16825). It proves a modulo-Φₙ(q)² congruence for a different binomial-type sum and cites the source only in a general reference list. An arXiv sweep of 2025–2026 papers mentioning Van Hamme or creative microscoping was done, reading those touching (E.2)/(F.2) or Guo's conjectures: Karmakar–Jana arXiv:2610.11786 and 2610.11778, Liu–Tao arXiv:2606.12037 (two other conjectures of Guo), arXiv:2606.08624, and Wang–Tian–Huang 2505.04395. None treats Conjecture 4.1. The omega registry's issues and pull requests (searched for the arXiv id, "Guo Wang q-supercongruence", "supercongruence Phi_n(q)^4" and "Guo Wang Conjecture 4.1"), the Principia list and archive, and the mio-qwq and openai/math clones have no entry. The journal body is still unread, because ScienceDirect's robots.txt disallows all agents. Residual risk: about 5%.

## Limitations

- The Lean certificate trusts the pinned Lean 4.34.1 toolchain and the pinned Mathlib build; Mathlib was not rebuilt.
- The journal body of the source was not read (flag JOURNAL_TEXT_UNREAD; the publisher's robots.txt disallows automated access). The citation census is now complete (four of four citing works identified).
- Nothing has been submitted or published.
