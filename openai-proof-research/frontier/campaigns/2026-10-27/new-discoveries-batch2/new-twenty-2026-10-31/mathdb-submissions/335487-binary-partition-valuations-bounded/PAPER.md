# Bounded 2-adic valuations of m-coloured binary partitions: a counterexample family to a conjecture of Gawron, Miska and Ulas

*Claude Opus 5.5 produced the written proof, Lean code and first review. GPT-6.2 Sol
performed the cross-model review and edited this manuscript. The theorem statements below were
kernel-checked in Lean 4 with Mathlib. The replay recorded only the axioms propext, Classical.choice
and Quot.sound.*

## Abstract

Let b_m(n) be the number of partitions of n into powers of 2 in which every part carries one of m
colours. Gawron, Miska and Ulas conjectured that ν₂(b_m(n)) is unbounded in n for every m ≥ 2 that is
not of the form 2^k − 1. We show that this is false:

- ν₂(b₁₁(n)) ≤ 4 for every n.
- More generally, ν₂(b_m(n)) ≤ 4 for every n and every m = 2^K(4^j + 1) − 1 with K ≥ 4 and j ≥ 1.
  The smallest members are 79, 159, 271, 319, 543, 639 and 1039.

The proof works modulo 32. The congruence H_m ≡ (1−x)^N T^{N−m} turns b_m mod 32 into a finite
polynomial automaton. For the two-parameter family, closure under pairs of binary digits
reduces all j to a single finite check. Dilation reduces K ≥ 4 to K = 4. All of
this is formalized in Lean, including the bridge from the combinatorial definition of b_m.

## 1. The conjecture and the definitions

**Source.** Gawron, Miska and Ulas, *Arithmetic properties of coefficients of power series
expansion of ∏_{n≥0}(1 − x^{2^n})^t (with an appendix by Andrzej Schinzel)*, arXiv:1703.01955v1
(6 March 2017), Monatshefte für Mathematik 185 (2018), 307–360.
[Published article](https://doi.org/10.1007/s00605-017-1041-2)

Let T(x) = ∏_{i≥0}(1 − x^{2^i}), the generating function for the signs of the Thue–Morse
sequence. The source defines b_m(n) = [xⁿ]T(x)^{−m} in §4 and calls this generating function H_m.
The coefficients of H₁ count partitions into powers of 2, with an arbitrary nonnegative
multiplicity for each part size. The source identifies b_m with the m-fold convolution of
these counts.

Conjecture 5.3 (arXiv v1, p. 30 and journal p. 353) asserts that
(ν₂(b_m(n)))_{n≥0} is unbounded for every integer m ≥ 2 satisfying
m ≠ 2^k − 1 for all positive integers k.

**Lean definitions** (`src/BinStatement.lean`). We take the source's binary partition function literally:
`bin n` counts the partitions of n all of whose parts are powers of 2. A representation
n = Σ ε_i 2^i with ε_i ∈ ℕ is the same thing as such a partition, with ε_i the multiplicity of the part
2^i. b_m is the m-fold convolution of `bin`, which is the source's displayed formula, with `b 0` the
unit sequence:

```lean
def bin (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => ∀ i ∈ p.parts, ∃ k, i = 2 ^ k)).card

def b : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => ∑ ij ∈ Finset.antidiagonal n, bin ij.1 * b m ij.2

def Conjecture53 : Prop :=
  ∀ m : ℕ, 2 ≤ m → (∀ k : ℕ, 0 < k → m ≠ 2 ^ k - 1) →
    ∀ B : ℕ, ∃ n : ℕ, B < padicValNat 2 (b m n)
```

Here `Nat.Partition n` is Mathlib's type of multisets of positive integers summing to n, and
`padicValNat 2` is ν₂ on positive integers. For m ≥ 1, b_m(n) ≥ 1, so the convention for ν₂(0) does not matter.
Our theorems also show directly that 32 ∤ b_m(n), so b_m(n) ≠ 0.

**Checks against the source** (kernel-evaluated, `src/BinValues.lean`):
- `bin` agrees with A018819 for n ≤ 16 (1, 1, 2, 2, 4, 4, 6, 6, 10, 10, 14, 14, 20, 20, 26, 26, 36).
- b_m(0) = 1 and b_m(1) = m for all m (source, Lemma 4.1).
- b₁₁(0..15) = 1, 11, 77, 407, 1804, 6996, 24508, 78980, 237589, 673783, 1816177, 4681491, 11599632,
  27740240, 64256016, 144581712.
- ν₂(b₁₁(12)) = 4, since b₁₁(12) = 2⁴ · 724977.

Lean derives (1−x)H₁(x) = H₁(x²) and T·H₁ = 1 from the combinatorial definition, then
identifies the coefficients of H₁^m with b_m reduced modulo 32 (Lemmas 2 and 4).

## 2. Results

**Theorem B.** For every n ≥ 0, 2⁵ ∤ b₁₁(n). So ν₂(b₁₁(n)) ≤ 4, with equality at n = 12. Since
12 is not a power of 2, m = 11 satisfies the hypotheses of Conjecture 5.3, so the conjecture is false.

**Theorem A.** For all integers K ≥ 4, j ≥ 1 and n ≥ 0, with m = 2^K(4^j + 1) − 1, we have
2⁵ ∤ b_m(n). So ν₂(b_m(n)) ≤ 4. The odd factor 4^j + 1 of m + 1 exceeds 1, so every member is an admissible
counterexample. Fixing K = 4 and varying j gives infinitely many distinct members.

Lean endpoints (`src/BinMain.lean`):

```lean
theorem mathdb_335487_refuted :
    ¬ (∀ m : ℕ, 2 ≤ m → (∀ k : ℕ, 0 < k → m ≠ 2 ^ k - 1) →
        ∀ B : ℕ, ∃ n : ℕ, B < padicValNat 2 (b m n))
theorem b11_not_dvd (n : ℕ) : ¬ 32 ∣ b 11 n
theorem family_not_dvd (K j n : ℕ) (hK : 4 ≤ K) (_hj : 1 ≤ j) :
    ¬ 32 ∣ b (2 ^ K * (4 ^ j + 1) - 1) n
theorem family_counterexample (K j : ℕ) (hK : 4 ≤ K) (hj : 1 ≤ j) :
    2 ≤ 2 ^ K * (4 ^ j + 1) - 1 ∧
    (∀ k : ℕ, 0 < k → 2 ^ K * (4 ^ j + 1) - 1 ≠ 2 ^ k - 1) ∧
    ∀ n : ℕ, padicValNat 2 (b (2 ^ K * (4 ^ j + 1) - 1) n) ≤ 4
```

The divisibility bound also holds at j = 0, where m = 2^{K+1} − 1 falls under the source's
Theorem 4.6.

## 3. Proof

All power series are in (ℤ/32)[[x]]. For a power series F, write F(x²) = D F, and D^a for the a-fold
iterate. In Lean, D is Mathlib's `PowerSeries.expand 2`, a ring homomorphism.

### 3.1 From partitions to functional equations

**Lemma 1** (`BinBridge.lean`). bin(0) = 1, and for n ≥ 0,
bin(n+1) = bin(n) + [2 ∣ n+1]·bin((n+1)/2).

*Proof.* Split the binary partitions of n+1 by whether they contain a part 1.
- Those that contain a part 1 correspond bijectively to the binary partitions of n: remove one 1, or add
  one 1.
- Those that do not contain a part 1 have only parts 2^k with k ≥ 1, so all parts are even. If n+1 is
  odd there are none. If n+1 = 2k, halving every part is a bijection onto the binary partitions of k,
  with doubling as its inverse.
- bin(0) = 1 because the only partition of 0 is the empty one. ∎

Let H₁ = Σ bin(n)xⁿ. Let T = Σ t_n xⁿ with t₀ = 1, t_{2n} = t_n, t_{2n+1} = −t_n, so
t_n = (−1)^{s₂(n)}, the source's F(x).

**Lemma 2** (`BinSeries.lean`).
(a) (1−x)H₁ = D H₁.
(b) T = (1−x) D T.
(c) T·H₁ = 1.
(d) T(1−x) = 1 + 2U for some U.
(e) (T(1−x))^16 = 1.

*Proof.*
- (a) is Lemma 1 read coefficientwise. (b) is the recurrence for t_n.
- (c): put G = T H₁. By (a) and (b), G = (1−x) DT · H₁ = DT · DH₁ = D G. Since G(0) = 1, strong
  induction on n gives coefficient 0 for every n ≥ 1: odd n gives 0 because DG has no odd terms, and
  for even n ≥ 2 the coefficient equals that of n/2.
- (d): for n ≥ 1 the coefficient of xⁿ in T(1−x) is t_n − t_{n−1} ∈ {0, ±2}.
- (e): in any commutative ring with 32 = 0, (B+2W)^16 = B^16. This follows by squaring four times:
  (B + 2^i V)² = B² + 2^{i+1}(BV + 2^{i−1}V²) for i ≥ 1, applied with the
  successive base powers B, B², B⁴ and B⁸. ∎

**Lemma 3** (★; `star`). If 16 ∣ N and m ≤ N, then H₁^m = (1−x)^N T^{N−m}.

*Proof.* Using (e) and then (c):
H₁^m = H₁^m (T(1−x))^N = (TH₁)^m (1−x)^N T^{N−m} = (1−x)^N T^{N−m}. ∎

**Lemma 4** (`coeff_H1_pow`). The coefficient of xⁿ in H₁^m is b_m(n) mod 32. This follows by induction
on m from the definition of b as an iterated convolution.

**Lemma 5** (`pw_dil`). For all a, c ≥ 0, (1−x)^{2^{a+4}c} = D^a((1−x)^{16c}).

*Proof.* Write (1−x)² = (1−x²) + 2(x²−x). By (B+2W)^16 = B^16 we get
(1−x)^{2·16M} = (1−x²)^{16M}. Then induct on a. ∎

### 3.2 The section automaton

Represent a polynomial by its coefficient list mod 32. For R ≥ 0 and ε ∈ {0,1}, let φ^R_ε(Q) be the
ε-section of Q(x)(1−x)^R, so that Q(1−x)^R = D φ^R_0(Q) + x D φ^R_1(Q).

**Lemma 6** (`step0`, `step1`). For every power series F,
[x^{2n+ε}] (Q·(1−x)^R·DF) = [xⁿ] (φ^R_ε(Q)·F).

By Lemma 2(b), T^R = (1−x)^R D(T^R). So [x^{2n+ε}](Q T^R) = [xⁿ](φ^R_ε(Q) T^R).

**Lemma 7** (`aut_sound`). Suppose a finite table of polynomials is closed (mod 32) under φ^R_0 and
φ^R_1, and every entry has constant term ≢ 0 mod 32. Then for every entry Q and every n,
[xⁿ](Q T^R) ≢ 0 (mod 32).

*Proof.* Strong induction on n. The case n = 0 is the constant-term condition. The case n = 2k+ε ≥ 1
reduces by Lemma 6 to k < n. ∎

### 3.3 Proof of Theorem B

By Lemmas 3 and 4 with N = 16, b₁₁(n) ≡ [xⁿ]((1−x)^16 T^5) (mod 32). The closure of (1−x)^16 under
φ^5_0 and φ^5_1 has 70 states (`tbl11`). No state has constant term ≡ 0 mod 32; the largest 2-adic
valuation among the constant terms is 4. Lemma 7 then gives 32 ∤ b₁₁(n) for every n. The negation of
the conjecture follows from B = 4, because 11 ≠ 2^k − 1 for every k. ∎

### 3.4 Proof of Theorem A

Write K = a + 4 and u = 4^j + 1, so m = 2^{a+4}u − 1. By Lemma 3 with N = m + 1 and N − m = 1, and then
Lemma 5, using 16u = 16 + 2^{2j+4}:

H_m ≡ (1−x)^{2^{a+4}u} T = D^a(F) · T,  where F = (1−x)^16 · D^{2j}((1−x)^16).

Indeed, Lemma 5 first extracts D^a, then rewrites the factor (1−x)^{2^{2j+4}} as
D^{2j}((1−x)^16).

**K-direction** (`dil_sound`). If every coefficient of F·T is nonzero mod 32, then so is every
coefficient of D^a(F)·T. Indeed, D(C)·T = (1−x)·D(C·T), so by Lemma 6 with Q = 1:
- [x^{2q}](DC·T) = [x^q](C·T);
- [x^{2q+1}](DC·T) = −[x^q](C·T), because φ¹₀(1) = 1 and φ¹₁(1) = −1.

Induct on a. This is the source's self-similarity for 2^k − 1, transplanted.

**j-direction** (`fam_sound`). Let G = (1−x)^16. Using D(C)·T = (1−x)D(C·T) twice, Lemma 6 shows that
for a polynomial Q and n = 4q + 2f + e:

[xⁿ](Q · D^{2k+2}G · T) = [x^q](ψ_{ef}(Q) · D^{2k}G · T),  with ψ_{ef} = φ¹_f ∘ φ¹_e.

Let S be the closure of G under the four maps ψ_{ef} (mod 32). It has 31 elements (`famS`). For each
Q ∈ S, the polynomial Q·G lies in a 400-state table (`famTbl`) that is closed under φ¹_0 and φ¹_1, and
no state of that table has constant term ≡ 0 mod 32. Lemma 7 (R = 1) gives the case k = 0 for every
Q ∈ S. Induction on k then gives, for every k, every Q ∈ S and every n:

[xⁿ](Q · D^{2k}G · T) ≢ 0 (mod 32).

Take Q = G and k = j. Then F·T has no coefficient ≡ 0 mod 32, and the K-direction completes the proof. ∎

The exponent 4^j gives a separation of 2j binary digits. Closing under single-digit steps
instead yields 57 polynomials, and the corresponding base table has 672 states, six with
zero constant term. Odd separation can violate the bound. The source recurrence gives b₄₇(52) ≡ 64 (mod 128). The original
written proof instead separates the Thue–Morse factors and handles the carry with
t(4^j − d) = t(d − 1) for 1 ≤ d ≤ 4^j. For j ≥ 2 this reduces the carry cases to sixteen
55-state automata.

### 3.5 Computation and its verification

The tables were generated by `scripts/automata.py` using exact arithmetic modulo 32.
Lean's checkers `checkAut`, `rowOK` and `checkFam` verify the constant terms, destination
indices and polynomial transitions against the list operations `mulL`, `sect` and `pwL`.
The soundness lemmas connect those operations to the series semantics `toPS`. The kernel
evaluates the checks via `decide +kernel`, including eight batches of 50 rows for the
family's base table. The cross-model review independently regenerated the closures and
checked the rows against the actual Lean tables.

## 4. Significance

Gawron, Miska and Ulas gave the exact valuations for m = 2^k − 1 and reported extensive
computations for m = 2, including residue classes with fixed valuations. In 2023,
Sobolewski and Ulas proved that b_m modulo each fixed power of 2 is 2-automatic and
restated Conjecture 5.3 as open.
[Source Theorem 4.6 and §5](https://doi.org/10.1007/s00605-017-1041-2)
[Sobolewski–Ulas §7](https://doi.org/10.1007/s00025-023-01966-8)

Coefficient scans quickly flag m = 11, and a standard finite-state check proves the
bound for this fixed exponent. Theorem A supplies a uniform bound over an explicit
infinite family. Its main step is to handle the separation between the two nonzero
binary digits of m + 1, using a closure that works for every separation of even length.
The dilation in K uses the self-similarity behind the source's Mersenne case. The theorem
leaves the classification of bounded exponents open.

## 5. Prior work

The cross-model review checked the sole arXiv version and the published source,
citing literature, the Omega and Principia registries, and relevant OEIS entries.
The searches located no earlier resolution. Sobolewski and Ulas, Proposition 7.3 and
the paragraph following it, provide the closest prior result and explicitly discuss
the same conjecture. Ulas and Żmija's work on colored p-ary partitions covers odd primes,
and their paper on modified colored partitions uses an extra factor (1−x)^{−m} in
the generating function. The 2026 preprints on other conjectures of Gawron, Miska and
Ulas treat positive powers of T.
[Sobolewski–Ulas](https://arxiv.org/abs/2211.16622)
[Ulas–Żmija on odd primes](https://arxiv.org/abs/1809.04628)
[Ulas–Żmija on modified partitions](https://arxiv.org/abs/1904.03398)

## 6. Lean map

| Module | Content |
|---|---|
| `BinStatement` | `bin`, `b`, `Conjecture53` (literal definitions) |
| `BinBridge` | Lemma 1 (bijections on `Nat.Partition`) |
| `BinSeries` | Lemma 2–5: `T_func`, `H1_func`, `T_mul_H1`, `pow16`, `T_one_sub_X_pow16`, `star`, `coeff_H1_pow`, `pw_dil` |
| `BinAutomaton` | lists as polynomials, `split_mul`, `step0/1`, `rowOK`, `checkAut`, `aut_sound` |
| `BinData11` | 70-state table for m = 11, `check11` by kernel evaluation |
| `BinFamilyCheck` | `checkFam`, `digit0/1`, `fam_sound` (j-direction), `dil_sound` (K-direction) |
| `BinDataFamily` | `famS` (31), `famTbl` (400), chunked kernel checks |
| `BinMain` | endpoints |
| `BinValues` | exact small values: A018819, Lemma 4.1, b₁₁(0..15), ν₂(b₁₁(12)) = 4 |
| `BinAxioms` | statements and `#print axioms` |

## References

1. M. Gawron, P. Miska and M. Ulas, *Arithmetic properties of coefficients of power series
   expansion of ∏_{n≥0}(1 − x^{2^n})^t (with an appendix by Andrzej Schinzel)*,
   Monatshefte für Mathematik 185 (2018), 307–360.
   [Published article](https://doi.org/10.1007/s00605-017-1041-2)
2. B. Sobolewski and M. Ulas, *Values of Binary Partition Function Represented by a Sum of Three Squares*,
   Results in Mathematics 78 (2023), article 188.
   [Published article](https://doi.org/10.1007/s00025-023-01966-8)
3. M. Ulas, *2-Adic valuations of coefficients of certain integer powers of formal power series*,
   International Journal of Number Theory 15 (2019), 723–762.
   [Published article](https://doi.org/10.1142/S1793042119500386)
4. [OEIS A018819](https://oeis.org/A018819).
