# Common denominators of the Fabius function: Conjecture 16

## Abstract

We prove all three clauses of Arias de Reyna's Conjecture 16 about the least common denominators of the odd dyadic values of the Fabius function. An integral triangular Thue–Morse convolution and propagation of local integer-valued polynomials identify the odd-prime denominator exponents with maxima of moment-coefficient denominator exponents. A first-weighted-minimum argument gives the required factorial divisibility. The exact exponent at 2 makes the final quotients odd. The Lean certificate includes the analytic evaluator bridge and least-denominator semantics. Non-vacuity and uniqueness are supplied by an explicitly attributed, separately included public ProveIt existence proof, rather than assumed.

**Attribution and scope.** This certificate builds on Vladimir Reshetnikov and the ProveIt Contributors’ public library, pinned at `39d36e129589eed9edc5f2d40acfa683d783501d` under the MIT No Attribution License. Twelve inherited modules (6,173 lines) supply the established arithmetic, definitions and analytic evaluator bridge; the copied conjecture definition contributes another nine lines, and the separately included existence and uniqueness construction contributes 809 lines. The inherited modules retain their proof statements, with import renaming and two redundant tactic removals; the existence file is unchanged after its attribution header. The new contribution is the common-denominator argument and its formalization and integration, not the Fabius construction or the public library. Exact accounting appears in §9.

## Source statement and definitions

The source is J. Arias de Reyna, *Arithmetic of the Fabius function*, [arXiv:1702.06487v3](https://arxiv.org/abs/1702.06487v3), §§1.1, 6–8. Conjecture 16 is Conjecture 1 in the journal version, *Integers* 18 (2018), A51. The MathDB record is 335354. The source PDF is retained as `sources/1702.06487v3.pdf`; pages 11–12 were rendered and visually checked for the following transcription. Source quotations below preserve the printed wording and mathematical expressions, including the typographical “le”.

The source's §1.1 describes its globally signed function by:

> “Secondly, the Fabius function \(F(x)\), defined by Fabius, that satisfies \(F'(x)=2F(2x)\) for \(x>0\).”

For its unit-interval restriction it says:

> “The Fabius function \(F\colon[0,1]\to[0,1]\) is increasing with \(F(0)=0\) and \(F(1)=1\).”

Its displayed definition of the folded function is
\[
 \operatorname{up}(t)=
 \begin{cases}
 F(t+1)&\text{for }-1\le t\le0,\\
 F(1-t)&\text{for }0\le t\le1,\\
 0&\text{for }|t|>1.
 \end{cases}
\]
The source also specifies smoothness and compact support, the normalization \(\operatorname{up}(0)=1\), and the equation
\[
 \operatorname{up}'(x)=2\bigl(\operatorname{up}(2x+1)-\operatorname{up}(2x-1)\bigr). \tag{S2}
\]
The globally signed continuation in source (1) is distinct from the constant-tail bounded function used below. Only their common restriction to \([0,1]\) enters the conjecture.

Definition 12 reads:

> “Let \(D_n\) be le least common multiple of the denominators of the fractions \(\operatorname{up}(\frac{2k+1}{2^n})\) with \(2^{-n}<2k+1\le2^n\).”

The printed lower bound is \(2^{-n}\), not \(-2^n\). For \(n\ge1\) this selects exactly the positive odd numerators \(1,3,\ldots,2^n-1\); the upper endpoint is even. For \(n=0\) the set is empty and its lcm is 1, agreeing with the displayed \(D_0=1\). Allowing negative numerators would give the same lcm by evenness, but that is not the transcription used here.

**Conjecture 16 (verbatim, with mathematical typesetting).**

> “The following appear to be true:
>
> (a) The quotient \(A_n=2^{-\binom n2}D_n\) satisfies \(A_{2n}=A_{2n+1}\) for \(n\ge1\).
>
> (b) Let \(K_n=A_{2n-1}\) for \(n\ge1\), so that by (a) we have \(K_1=A_1\), and for \(n\ge2\)
> \[
> K_n=2^{-\binom{2n-1}{2}}D_{2n-1}=2^{-\binom{2n-2}{2}}D_{2n-2}.
> \]
> Then \(2\times(2n-1)!\) divides \(K_n\).
>
> (c) The quotients \(H_n=\frac{K_n}{2(2n-1)!}\) are odd integers.”

The other sequences used in the proof are defined in source (8) and (21):
\[
 c_n=\int_{\mathbb R}t^{2n}\operatorname{up}(t)\,dt,
 \qquad d_n=n\int_0^1t^{n-1}\operatorname{up}(t)\,dt\quad(n\ge1),
\]
with \(c_0=d_0=1\). Their rational recurrences are displayed in the proof below and in source (10), (19). We do not identify an arbitrary recurrence with these analytic quantities merely by notation: the certificate proves the dyadic evaluator bridge needed for the conjecture.

### The corresponding Lean definitions

The standard bounded characterization is the public ProveIt definition, copied unchanged in `UpstreamBasic.lean`:

```lean
abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev BoundedFabius := ℝ → UnitInterval
abbrev fabiusReal (F : BoundedFabius) : ℝ → ℝ := fun x => F x
structure IsFabius (F : BoundedFabius) : Prop where
  zero_of_nonpos : ∀ x, x ≤ 0 → fabiusReal F x = 0
  one_of_one_le : ∀ x, 1 ≤ x → fabiusReal F x = 1
  contDiff : ContDiff ℝ ∞ (fabiusReal F)
  symmetry : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    fabiusReal F (1 - x) = 1 - fabiusReal F x
  hasDerivAt : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
    HasDerivAt (fabiusReal F) (2 * fabiusReal F (2 * x)) x
noncomputable def rvachevUp (F : BoundedFabius) (x : ℝ) : ℝ :=
  if x ≤ 0 then fabiusReal F (x + 1) else fabiusReal F (1 - x)
```

The constant tails make this `rvachevUp` exactly the displayed source folding, including outside the support. The imported differential lemmas prove (S2) for it. In particular, the bounded characterization is used on the domain on which the source's \(F\) takes values in \([0,1]\); the certificate does not assert that its constant-tail extension satisfies the globally signed function's derivative equation for all real \(x\).

The rational definitions below are literal excerpts from `UpstreamArithmetic.lean`; all operations occur in \(\mathbb Q\) until the finite lcm is taken in \(\mathbb N\).

```lean
def moment : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1),
          (Nat.choose (2 * (n + 1) + 1) (2 * k.val) : ℚ) * moment k.val) /
        (((2 * (n + 1) + 1 : ℕ) : ℚ) * ((2 : ℚ) ^ (2 * (n + 1)) - 1))
termination_by n => n
decreasing_by exact k.isLt

def halfMoment : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) /
        (((n + 2 : ℕ) : ℚ) * ((2 : ℚ) ^ (n + 1) - 1))
termination_by n => n
decreasing_by exact k.isLt

def fabiusDyadic (n a : ℕ) : ℚ :=
  (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
    ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
      ∑ k : Fin (n / 2 + 1),
        (Nat.choose n (2 * k.val) : ℚ) *
          ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) * moment k.val

def rvachevDyadic (n : ℕ) (a : ℤ) : ℚ :=
  if a.natAbs ≤ 2 ^ n then
    |fabiusDyadic n (2 ^ n - a.natAbs)|
  else
    0

def oddDyadicNumerators (n : ℕ) : Finset ℕ :=
  (Icc 1 (2 ^ n - 1)).filter Odd

def dyadicDenominator (n : ℕ) : ℕ :=
  (oddDyadicNumerators n).lcm fun a => (rvachevDyadic n a).den

def normalizedDyadicDenominator (n : ℕ) : ℚ :=
  dyadicDenominator n / (2 : ℚ) ^ n.choose 2

/-- The sequence `K_n = A_(2n-1)` from Conjecture 16. -/
def conjecturalK (n : ℕ) : ℚ :=
  normalizedDyadicDenominator (2 * n - 1)

/-- The sequence `H_n = K_n / (2 (2n-1)!)` from Conjecture 16. -/
def conjecturalH (n : ℕ) : ℚ :=
  conjecturalK n / (2 * (Nat.factorial (2 * n - 1) : ℚ))
```

`IsOddNatural q` is `∃ m : ℕ, Odd m ∧ q = m`. Divisibility is certified by an explicit natural quotient; no assertion of divisibility in a field is used. The public proposition `conjecture_sixteen` is the conjunction of the three printed assertions and the redundant predecessor identity in (b). Its exact statement appears in the appendix and report.

### Why the recurrence-defined denominator is the source denominator

Source (32) is
\[
 F(a/2^n)=\operatorname{up}(1-a/2^n)
 =\frac{2^{-\binom{n+1}{2}}}{n!}
 \sum_{h=0}^{a-1}(-1)^{w(h)}
 \sum_{k=0}^{\lfloor n/2\rfloor}\binom n{2k}
 (2a-2h-1)^{n-2k}c_k. \tag{S32}
\]
This is precisely `fabiusDyadic`. Source Proposition 10 gives another, Taylor-recursive evaluation: if \(2^{-n}\le x<2^{-n+1}\) and \(y=x-2^{-n}\), then
\[
 F(x)=-F(y)+\sum_{0\le k\le n}
 2^{\binom{k+1}{2}-\binom{n-k}{2}}
 \frac{d_{n-k}}{(n-k)!}\frac{y^k}{k!}. \tag{S35}
\]
For dyadic \(x\), repeatedly removing its leading binary digit terminates at zero. Thus both descriptions compute the same values, rather than postulating a different function. The Lean analytic modules establish the stronger precise bridge

```lean
Fabius.fabiusDyadic_cast (F : Fabius.BoundedFabius)
  (hF : Fabius.IsFabius F) (n a : ℕ) (ha : a ≤ 2 ^ n) :
  (Fabius.fabiusDyadic n a : ℝ) =
    Fabius.fabiusReal F ((a : ℝ) / (2 : ℝ) ^ n)
```

Reflection sends the positive odd grid to itself. The lane proves the reflected `rvachevDyadic` bridge, then uses the elementary equivalence
\[
 (\exists z\in\mathbb Z,\;dq=z)\quad\Longleftrightarrow\quad\operatorname{den}(q)\mid d
 \qquad(q\in\mathbb Q,\ d\in\mathbb N).
\]
Consequently `analytic_rvachev_common_denominator_iff` proves that a positive integer clears every analytic grid value exactly when `dyadicDenominator n` divides it, and `source_D_isLeast_analytic` proves leastness. These are checked Lean theorems, not informal semantic assumptions. Section 6 below supplies an actual function satisfying the characterization.

## 1. Source identities, with normalization fixed

Write \(c_j\) and \(d_j\) for the rational sequences of source equations (10), (19), and (23). We use only these already proved facts:

1. \(c_0=1\) and
   \[
   (2j+1)(2^{2j}-1)c_j=\sum_{i=0}^{j-1}\binom{2j+1}{2i}c_i.
   \tag{1}
   \]
2. The numbers \(c_j\) have odd denominators, by source (11), and \(v_2(d_n)=-1\) for \(n\ge1\), by source Theorem 20 (journal Theorem 5).
3. \(d_n=2^{-n}\sum_{j=0}^{\lfloor n/2\rfloor}\binom n{2j}c_j\).
4. Source (33) gives, for \(1\le a<2^n\),
   \[
   2^{\binom n2}F(a/2^n)
    ={1\over 2^n n!}\sum_{h=0}^{a-1}(-1)^{s_2(h)}
        \sum_{j=0}^{\lfloor n/2\rfloor}\binom n{2j}c_j(2a-2h-1)^{n-2j}.
   \tag{2}
   \]
   This is (33) with its \(\operatorname{up}(1-a/2^n)\) replaced by \(F(a/2^n)\); the two expressions are identical on this interval.

All power series below are formal over \(\mathbb Q\); no convergence, integration, or p-adic analytic theorem is used. Set
\[
 E(z)=\sum_{j\ge0}{c_j\over(2j)!}z^{2j}=\sum_{j\ge0}e_jz^j,
 \qquad h(z)=\sum_{j\ge0}{z^{2j}\over(2j+1)!}.
\]
Thus \(e_{2j}=c_j/(2j)!\), \(e_{2j+1}=0\), and \(e_0=1\). Dividing (1) by ((2j+1)!) gives exactly
\[
 E(2z)=h(z)E(z).\tag{3}
\]
Define the rational polynomial
\[
 Q_n(X)=[z^n]E(z)e^{Xz}
       =\sum_{j=0}^{\lfloor n/2\rfloor}{c_jX^{n-2j}\over(2j)!(n-2j)!}.
\tag{4}
\]
It has degree \(n\), constant coefficient \(e_n\), and
\[
 Q_n(1)/2^n=d_n/n!.
\tag{5}
\]
Using \(e^z-e^{-z}=2zh(z)\) and (3), coefficient comparison yields
\[
 Q_n(X+1)-Q_n(X-1)=2^nQ_{n-1}(X/2),\qquad n\ge1.
\tag{6}
\]
Indeed the generating series of the left side is \(2zE(2z)e^{Xz}\), whose degree-\(n\) coefficient is \(2^nQ_{n-1}(X/2)\).

## 2. An integral triangular convolution for the dyadic grid

Put \(s(b)=(-1)^{s_2(b)}\). Its elementary identities are \(s(2b)=s(b)\), \(s(2b+1)=-s(b)\). In (2) take \(a=2b+1\), and pair the terms \(h=2j,2j+1\). The last unpaired term is \(h=2b\). Equations (4)–(6) give
\[
 V_n(b):=2^{\binom n2}F((2b+1)/2^n)
       =\sum_{j=0}^b s(j)r_n(b-j),\quad 0\le b<2^{n-1},\tag{7}
\]
where
\[
 r_n(0)=d_n/n!,\qquad r_n(b)=Q_{n-1}(2b)\quad(b\ge1).
\tag{8}
\]
For clarity, the paired summand before simplification is
\[
 {Q_n(4(b-j)+1)-Q_n(4(b-j)-1)\over2^n};
\]
(6) turns it into \(Q_{n-1}(2(b-j))\).

Because \(s(0)=1\), (7) is a triangular integer matrix with diagonal 1. Its inverse is also integral, by solving successively for each \(r_n(b)\). Thus the lists of \(V_n(b)\) and \(r_n(b)\), for the same finite range of \(b\), have the same common denominator, prime by prime.

In particular the common denominator of the \(V_n(b)\) is \(A_n\). To justify that \(A_n\) is an integer rather than assume it: \(V_n(0)=d_n/n!\) has 2-adic valuation \(-1-v_2(n!)\), so \(v_2(D_n)\ge\binom n2+1+v_2(n!)\). Multiplication of the original dyadic values by \(2^{\binom n2}\) therefore divides their common denominator by exactly this power of 2.

## 3. Local polynomial denominators

Fix an odd prime \(p\), put \(R=\mathbb Z_{(p)}\), and give zero valuation \(+\infty\). For a rational polynomial \(P\), let
\[
 b(P)=\min\{a\ge0:p^aP(x)\in R\text{ for all }x\in R\}.
\]
The minimum exists, since clearing the coefficients is sufficient.

We need two elementary integer-valued-polynomial facts.

**Density fact.** If \(P\) takes values in \(R\) on all integers, on all even integers, or on all odd integers, then \(P(R)\subseteq R\). To see this, choose \(t\ge0\) with \(p^tP\in R[X]\). For any \(x\in R\), choose an integer in the indicated residue class modulo 2 that is congruent to \(x\) modulo \(p^tR\); modular inversion of the denominator of \(x\), followed by the Chinese remainder theorem, supplies it. Polynomial evaluation is congruence-preserving in (R[X]), so \(P(x)-P(a)\in R\). The same proof works on \(2\mathbb Z\) after scaling the input by 2.

**Finite sampling fact.** A polynomial of degree at most \(d\) takes values in \(R\) on every integer if and only if it does so on (d+1) consecutive integers. Repeated differences express it as
\[
 P(X)=\sum_{j=0}^d\Delta^jP(a)\binom{X-a}{j}.
\]
The coefficients \(\Delta^jP(a)\) belong to \(R\), and the binomial polynomials take integer values at every integer, including negative integers. This proves the assertion. Together with the density fact, it also determines (b(P)) from those finitely many samples.

Let \(b_n=b(Q_n)\). Equation (6), and the fact that 2 is a unit in \(R\), show that
\[
 b_n\ge b_{n-1}.
\tag{9}
\]
If \(a\ge b_{n-1}\) and \(p^aQ_n(0)\in R\), the identity
\[
 p^aQ_n(X+2)-p^aQ_n(X)=2^np^aQ_{n-1}((X+1)/2)
\]
propagates integrality from 0 to every even integer in both directions. The density fact then proves \(a\ge b_n\). Since \(Q_n(0)=e_n\), induction gives
\[
 b_n=\max_{0\le j\le n}\{0,-v_p(e_j)\}.
\tag{10}
\]
Starting instead at 1 and propagating to all odd integers gives the equally useful identity
\[
 b_n=\max\{b_{n-1},0,-v_p(Q_n(1))\}.
\tag{11}
\]

For \(n\ge3\), the finite list \(1\le b<2^{n-1}\) contains the \(n\) consecutive values \(1,\ldots,n\), since \(2^{n-1}-1\ge n\). The polynomial \(Q_{n-1}(2X)\) has degree (n-1); by finite sampling and the fact that 2 is a unit, the maximum p-denominator exponent among these values is \(b_{n-1}\). Equations (5), (7), (8), and (11) now imply
\[
 \boxed{v_p(A_n)=b_n=\max_{0\le j\le n}\{0,-v_p(e_j)\}}
 \qquad(p\text{ odd},\ n\ge3).
\tag{12}
\]
At \(n=1,2\), direct evaluation gives \(A_1=2\), \(A_2=36\); the right sides of (12) are respectively 0 and \(v_p(9)\). Thus (12) holds for every \(n\ge1\).

## 4. The new weighted-valuation lemma

**Lemma.** For every odd prime \(p\) and integer \(N\ge0\),
\[
 \max_{0\le j\le N}\{0,-v_p(e_j)\}\ge
 \left\lfloor{N\over p-1}\right\rfloor.
\tag{13}
\]

**Proof.** If \(N<p-1\), the assertion is immediate. Otherwise, iterate (3) (p-1) times and put
\[
 T=2^{p-1},\qquad H(z)=\prod_{i=0}^{p-2}h(2^iz).
\]
Then
\[
 E(Tz)=H(z)E(z).\tag{14}
\]
Write \(H(z)=\sum H_lz^l\). The standard factorial valuation bound
\[
 v_p((m+1)!)\le {m\over p-1}\tag{15}
\]
follows from Legendre's formula \(the digit sum of (m+1>0) is at least 1\). Consequently each coefficient of each \(h(2^iz)\) has
\[
 (p-1)v_p(\text{coefficient of }z^m)+m\ge0.
\]
Products and the ultrametric inequality preserve this bound, so
\[
 (p-1)v_p(H_l)+l\ge0.\tag{16}
\]
For \(0<l<p-1\), all factorial denominators that occur are p-units, so the left side of (16) is strictly positive whenever \(H_l\ne0\).

At degree (p-1), any product term that uses two or more nonconstant factors again has p-integral coefficients: all its positive individual degrees are smaller than (p-1). The terms that use just one nonconstant factor sum to
\[
 {\sum_{i=0}^{p-2}2^{i(p-1)}\over p!}.
\]
By Fermat's theorem its numerator is \(p-1\not\equiv0\pmod p\). The remaining product terms are p-integral. Therefore
\[
 v_p(H_{p-1})=-1.\tag{17}
\]

Among the nonzero \(e_i\), \(0\le i\le N\), choose the **first** index \(j\) minimizing
\[
 W_i=(p-1)v_p(e_i)+i.
\]
This minimum exists because \(e_0=1\), and \(W_j\le0\). Suppose \(n=j+p-1\le N\). Comparing degree-\(n\) coefficients in (14), with \(H_0=1\), gives
\[
 (T^n-1)e_n=\sum_{l=1}^n H_le_{n-l}.\tag{18}
\]
Measure each degree-\(n\) term by \((p-1)v_p(\text{term})+n\). The term \(l=p-1\) on the right has measure exactly \(W_j\), by (17). If \(l<p-1\), its measure is strictly larger than \(W_j\), by the strict version of (16) and the minimality of \(W_j\). If \(l>p-1\), then \(n-l<j\), so its measure is also strictly larger than \(W_j\), by the **first-minimum** choice and (16). Zero terms may simply be omitted.

Hence the right side of (18) has a unique term of least p-adic valuation, so the sum has measure exactly \(W_j\). On the left, \(p\mid T^n-1\), again by Fermat, whereas \(W_n\ge W_j\). Thus the left side is zero or has measure at least \(W_j+p-1\). This is a contradiction.

It follows that \(j>N-(p-1)\). Since \(W_j\le0\),
\[
 -v_p(e_j)\ge\left\lceil{j\over p-1}\right\rceil
 \ge\left\lfloor{N\over p-1}\right\rfloor.
\]
For the last inequality, write \(N=q(p-1)+r\) with \(0\le r<p-1\), and use \(j\ge(q-1)(p-1)+r+1>(q-1)(p-1)\). This proves the lemma. \(\square\)

## 5. Exact 2-adic exponent and conclusion

The source gives \(v_2(r_n(0))=v_2(d_n/n!)=-1-v_2(n!)\). Every \(c_j\) has odd denominator. Formula (4) consequently gives
\[
 v_2(Q_{n-1}(2b))\ge-v_2((n-1)!)\qquad(b\in\mathbb Z),
\]
because each term in the equivalent form
\[
 Q_{n-1}(2b)={1\over(n-1)!}
 \sum_j\binom{n-1}{2j}c_j(2b)^{n-1-2j}
\]
has that lower bound. Equation (7) is unimodular over the integers, so
\[
 \boxed{v_2(A_n)=1+v_2(n!)}\qquad(n\ge1).
\tag{19}
\]

Because \(e_{2m+1}=0\), formula (12) gives identical odd-prime exponents for \(A_{2m}\) and \(A_{2m+1}\). Formula (19) gives identical 2-adic exponents because (2m+1) is odd. This proves \(a\).

For \(b\), set \(N=2m\). Equations (12), (13), and (15) give for every odd prime \(p\)
\[
 v_p(A_{2m+1})\ge\left\lfloor{2m\over p-1}\right\rfloor
 \ge v_p((2m+1)!).
\]
Equation (19) gives \(v_2(A_{2m+1})=1+v_2((2m+1)!)\). Thus \(2(2m+1)!\mid A_{2m+1}\). This is precisely \(b\) after replacing (m+1) by \(n\), including \(m=0\) since \(A_1=2\).

The quotient has 2-adic valuation zero by (19), so it is an odd integer. This proves \(c\). All three source assertions are now proved. \(\square\)


## 6. Certified existence and uniqueness (third-party construction)

The arithmetic proof above needs no analysis. To make its analytic interpretation non-vacuous, this packet includes Vladimir Reshetnikov's public ProveIt existence proof, not an existence assumption. The source is `Analysis/FabiusFunction/Lean/FabiusFunction/Existence.lean` at commit `39d36e129589eed9edc5f2d40acfa683d783501d`. Its theorem is `Fabius.existsUnique_fabius : ∃! F : BoundedFabius, IsFabius F`. This is existing mathematics and existing formalization, not a contribution claimed here.

Here is the construction that is checked. Let \(\mathcal C\) be the complete sup-norm space of continuous maps \([0,1]\to\mathbb R\), and let \(\mathcal A\) be its closed subspace consisting of functions valued in \([0,1]\) with \(f(1-x)=1-f(x)\). It is nonempty because \(f(x)=x\) belongs to it. Extend \(f\) continuously by clamping its argument to \([0,1]\), and write \(J_f(y)=\int_0^y f(t)\,dt\) on the unit interval. Symmetry gives \(J_f(1)=1/2\). Define
\[
 (Tf)(x)=\begin{cases}J_f(2x),&x\le1/2,\\
 1-J_f(2-2x),&x>1/2.
 \end{cases}
\]
The two branches agree at \(1/2\), and the integral bounds and reflection show that \(T\) maps \(\mathcal A\) to itself. For \(f,g\in\mathcal A\), the integral of \(f-g\) over the whole interval is zero. For \(0\le y\le1\), bounding either its integral on \([0,y]\) or its negative integral on \([y,1]\) yields
\[
 |J_f(y)-J_g(y)|\le \min(y,1-y)\|f-g\|_\infty
 \le\tfrac12\|f-g\|_\infty.
\]
Thus \(T\) is a contraction of ratio \(1/2\). Mathlib's Banach fixed-point theorem gives a fixed candidate \(f\). The fixed-point equation gives \(f(0)=0\), and symmetry gives \(f(1)=1\), so its clamped extension \(F\) has the required constant tails.

The fundamental theorem of calculus differentiates both branch formulas. At the gluing points \(0,1/2,1\), the derivative limits agree because the endpoint values are 0 and 1. This proves globally
\[
 F'(x)=2\operatorname{up}_F(2x-1).
\]
Folding then gives the Rvachev refinement equation (S2), including its gluing points. A differentiable solution of that equation is \(C^\infty\): if it is \(C^r\), its displayed derivative is \(C^r\), so it is \(C^{r+1}\); induction supplies every finite order. The displayed formula for \(F'\) transfers this smoothness to \(F\). On \([0,1/2]\), the fold is \(\operatorname{up}_F(2x-1)=F(2x)\), proving the last field of `IsFabius`. This certifies existence with no unproved analytic premise.

For uniqueness, the already checked `fabiusDyadic_cast` makes two `IsFabius` functions equal on all dyadics in the unit interval. For each \(x\in[0,1]\), the dyadics \(\lfloor2^nx\rfloor/2^n\) converge to \(x\). Continuity therefore gives equality at \(x\); the constant tails give equality outside. This is the imported `IsFabius.eq` theorem.

## 7. Endpoints and proof-to-code correspondence

The arithmetic endpoint `FabiusProofLane.mathdb335354_arithmetic` states the three printed assertions, with explicit natural quotients. It depends only on `LiteralConjectureSixteen` and its arithmetic dependencies. The original, stronger four-conjunct proposition remains proved by `FabiusProofLane.conjecture_sixteen_proved`.

The final endpoint is:

```lean
theorem arias_de_reyna_conjecture_16 :
    ∃! F : Fabius.BoundedFabius, Fabius.IsFabius F ∧
      Fabius.conjecture_sixteen ∧
      ∀ n : ℕ, IsLeast
        {d : ℕ | 0 < d ∧ ClearsAnalyticRvachev F n d}
        (Fabius.dyadicDenominator n)
```

Here the denominator predicate is literally

```lean
def ClearsAnalyticRvachev (F : Fabius.BoundedFabius) (n d : ℕ) : Prop :=
  ∀ a ∈ Fabius.oddDyadicNumerators n,
    ∃ z : ℤ, (d : ℝ)*Fabius.rvachevUp F ((a : ℝ)/(2 : ℝ)^n)=(z : ℝ)
```

Thus the theorem exhibits the unique standard bounded Fabius function and proves all clauses for the recurrence-defined numbers which are certified to be the least denominators of its actual analytic values. `certified_fabius_exists` separately exposes non-vacuity.

| Written step | Lean modules / representative declarations |
|---|---|
| Moment recurrence and rescaling coefficients | `SourceMomentBridge`, `ExplicitCoefficients`, `DilationSeries` |
| Weighted first minimum | `WeightedMinimumCore`, `WeightedMinimumArithmetic`, `KernelCoefficients`, `CoefficientDenominator.coefficient_denominator_witness` |
| Appell difference and integer-valued propagation | `SourceAppell`, `LocalPolynomial`, `AppellLocalDenominators.clearsLocal_iff_prefix_constants`, `FiniteSampling` |
| Thue–Morse convolution and inverse integrality | `DyadicAppellBridge`, `ThueMorseConvolution`, `TriangularDenominators` |
| Local common-denominator characterization | `DyadicLocalCharacterization.full_dyadic_grid_local_coefficients_iff`, `RationalLCM` |
| Exact power of 2, factorial bound, normalization | `TwoAdicGrid.normalizedGridLCM_two`, `NaturalGridResults`, `RawGridNormalization`, `SourceNormalization` |
| Literal conjecture and analytic leastness | `LiteralConjectureSixteen`, `AnalyticDenominatorEndpoint` |
| Existing analytic evaluator and existence | the twelve `Upstream*` modules and third-party `ProveItExistence` |
| Non-vacuous final packaging | `ArithmeticEndpoint`, `UnconditionalEndpoint` |

The written proof uses formal-series notation for clarity; the arithmetic Lean modules implement finite coefficient convolutions and finite valuation arguments. No convergence or p-adic field construction is needed. Rational zero is explicitly separated when using valuations; the paper's convention \(v_p(0)=+\infty\) is notation for those separate cases. Natural subtraction in the implementation is guarded by the stated index bounds.

## 8. Prior work and scope of the claim

The source's Theorem 13 gives the upper bound
\[
 D_n\mid n!\,2^{\binom{n+1}{2}}
 (2\lfloor n/2\rfloor+1)!!
 \prod_{k=1}^{\lfloor n/2\rfloor}(2^{2k}-1).
\]
Proposition 15 gives the single-value lower bound
\[
 \operatorname{den}\!\left(\frac{d_n}{2^{\binom n2}n!}\right)\mid D_n.
\]
Theorem 21 proves
\[
 v_2(F(2^{-n}))=-\binom n2-v_2(n!)-1 \quad(n\ge1).
\]
These do not give the required common-denominator odd-prime factorial bound: the source's quotient table contains 5, 55, 13, and 11, so a single sample does not always attain the lcm. The present argument uses the maximum over the entire coefficient prefix.

Vladimir Reshetnikov's [ProveIt](https://github.com/VladimirReshetnikov/ProveIt) already formalizes extensive Fabius arithmetic and analysis. Its public `conjecture_sixteen` and `IsFabius` are exactly the definitions used here. Its research-frontier material proves the 2-adic lower bound (`dyadicDenominator_padicVal_two_lower_bound`)
\[
 v_2(D_n)\ge\binom n2+v_2(n!)+1\qquad(n\ge1),
\]
not all three clauses. At the pinned commit its [coverage table](https://github.com/VladimirReshetnikov/ProveIt/blob/39d36e129589eed9edc5f2d40acfa683d783501d/Analysis/FabiusFunction/docs/PAPER_COVERAGE.md) and [walkthrough](https://github.com/VladimirReshetnikov/ProveIt/blob/39d36e129589eed9edc5f2d40acfa683d783501d/Analysis/FabiusFunction/docs/fabius_lean_walkthrough/fabius_lean_walkthrough%20%28part%20II%29.tex) keep Conjecture 16 open. A fresh final review on 2026-11-20 checked the newer public head `26ea07e90e25df22f3ea5fb682c6b74818a3f864` (committed 19:11:34 UTC): the coverage table and walkthrough still record no proof. A scan of all 992 current Fabius Lean files found only the conjecture definition, its conditional consequences, and existing denominator bounds, not an unconditional resolution. This is a bounded public-status check, not a worldwide-priority certificate. The supplied independent Claude Opus review checked every step of the new argument, reproduced the source's printed tables independently, and searched the public material without locating a proof. This lane re-fetched the pinned arithmetic and analytic sources and verified their equality with the inherited originals; it also checked the public documentation described in the provenance receipts. We rely on the review for its wider novelty search, not on the kernel checker as a novelty detector.

The review read the source versions and the relevant Bettin–Molteni–Sanna paper (2020), which concerns other identities rather than this common-denominator theorem. It did not read the body of Ahmed Sebbar's 2025 Monthly article: the manuscript download returned 403 and no refusal was bypassed. Its abstract concerns infinite products. This residual literature-access limitation remains explicit; no worldwide-priority claim is certified here. The review's broader searches and judgments are retained in `sources/REVIEW-335354.md`.

## 9. Third-party code and significance

The exact ProveIt commit is **`39d36e129589eed9edc5f2d40acfa683d783501d`**. Its pinned licence, read before fetching the existence source, is **MIT No Attribution License**, copyright 2026 ProveIt Contributors; it expressly permits use, copying, modification, and distribution. The licence text is retained in `sources/proveit-LICENSE-pinned`. We attribute the code to Vladimir Reshetnikov and ProveIt Contributors despite the absence of an attribution requirement.

All lines of the following inherited files are third-party-derived (including their documentation and locally renamed imports): `UpstreamArithmetic`, `UpstreamMomentPowerSeries`, `UpstreamNormalizedEvenMoments`, `UpstreamParity`, `UpstreamTwoAdic`, `UpstreamBasic`, `UpstreamThueMorseBitSupport`, `UpstreamAffineDifferenceOrbit`, `UpstreamDifferential`, `UpstreamDyadicCorrectness`, `UpstreamDyadicClosedForm`, and `UpstreamDyadicAnalytic`. They total 6,173 lines. They are copied unchanged from the reviewed lane; that lane renamed imports and removed two redundant tactic steps for Lean 4.34.1, with no theorem-statement change. `sources/proveit-analytic-files.json` preserves those exact patches. The public definition in `LiteralConjectureSixteen.lean`, lines 8–16, is also third-party text.

In the newly added `src/ProveItExistence.lean`, **lines 9–817** are the entire 809-line upstream file, byte-for-byte unchanged, including imports. Lines 1–8 are the attribution header. The raw file and content hashes are retained separately. The two one-line local modules `FabiusFunctionBasic` and `FabiusFunctionDyadicAnalytic` contain only imports; the build driver exposes their checked oleans at the public import paths so the existence source needs no edit. The report gives exact line ranges and all runner differences.

The contribution claimed for this packet is the proof of the three common-denominator assertions through the triangular transform, local polynomial propagation, and the finite weighted-minimum obstruction, together with its formal verification and analytic interpretation. The existence theorem, standard Fabius analysis, and source identities are prior work. A reasonable assessment is a concise elementary solution of a specialized arithmetic conjecture, rather than a broad structural breakthrough. The exact odd-prime prefix obstruction is the substantive arithmetic step beyond the published bounds. The kernel certificate establishes the displayed theorem relative to the pinned Mathlib trust base; it does not establish priority or rebuild every upstream Mathlib olean.
