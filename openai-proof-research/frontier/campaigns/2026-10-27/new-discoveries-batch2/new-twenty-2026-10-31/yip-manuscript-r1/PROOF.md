# Ordinary proof — MathDB 355956 (DRAFT, zero accepted credit)

Yip's maximal subfield clique conjecture is false: for q = 5^8 and d = 3, the prime field F_5 is a clique of GP(5^8, 3) but not a maximal clique, in every field with 5^8 elements.

This file gives the complete ordinary argument. Sections 1–6 are what the Lean module `proof/Yip355956.lean` certifies, in the form `MathDB355956.yip_conjecture_false` and `MathDB355956.yip_conjecture_SG_false`. Section 4 (irreducibility) and Section 7 are NOT Lean-certified: Section 4 is an ordinary supplement and Section 7 gives ordinary corollaries plus computational diagnostics. Root acceptance, final replay and paper review are pending.

## 0. Statement being refuted

Source: Yip, J. Algebraic Combin. 56(2) (2022) 323–333, arXiv:2101.09652, Conjecture 1.4. The same text appears as Conjecture 1.1 in Yip, Algebr. Comb. 6(4) (2023) 901–905, arXiv:2209.00864. MathDB 355956 reproduces it verbatim; the raw line is `sources/355956.jsonl`, sha256 4d6b71c7…b5a6d81d.

> Let d > 1 be an integer. Let q ≡ 1 (mod 2d) be a power of a prime p, and let r be the largest integer such that d | (q−1)/(p^r−1). Then the subfield F_{p^r} forms a maximal clique in GP(q,d).

Here GP(q,d) = Cay(F_q^+, (F_q^*)^d): vertices are the elements of F_q, and g ~ h iff g − h is a nonzero d-th power. A clique is a set of pairwise adjacent vertices. A maximal clique is a clique not contained in a strictly larger clique. The quantifiers are universal: every d > 1, every prime p, every power q of p with q ≡ 1 (mod 2d), with r determined by (q, d). The integrality of (q−1)/(p^r−1) is implicit and forces r ≥ 1 and r | m, where q = p^m. One admissible triple (q, d, r) at which F_{p^r} is not a maximal clique refutes the conjecture.

## 1. The parameters

q = 5^8 = 390625 and q − 1 = 390624 = 2^5 · 3 · 13 · 313 = 6 · 65104. Hence q ≡ 1 (mod 6) = (mod 2d).

For r ≥ 1, p^r − 1 divides p^m − 1 iff r | m, so r ∈ {1, 2, 4, 8}. The quotients (q−1)/(5^r−1) are:

| r | quotient |
|---|---|
| 1 | 97656 = 3 · 32552 |
| 2 | 16276 ≡ 1 (mod 3) |
| 4 | 626 ≡ 2 (mod 3) |
| 8 | 1 |

So the largest admissible r is 1, and the conjecture asserts that F_5 is a maximal clique of GP(5^8, 3).

Lean: `admissibleR_greatest`. It bounds r ≤ 8 and checks every r ≤ 8, including r = 3, 5, 6, 7, for which the quotient is not an integer.

## 2. Characteristic and the prime field

Let K be any field with 5^8 elements. Its characteristic is a prime dividing |K|, so it is 5.

In characteristic 5, z^5 − z = z(z−1)(z−2)(z−3)(z−4). Hence {z ∈ K : z^5 = z} = {0, 1, 2, 3, 4} = F_5.

Lean: `five_eq_zero_of_card`, `mem_subfieldSet_iff`. The formal `subfieldSet K 5` is literally {z | z^5 = z}.

## 3. A root of f = X^8 + X^7 + 2X^6 + 2 in K

Work in F_5[X]/(f), with t the class of X. Since X^8 ≡ 4X^7 + 3X^6 + 3, every class has a unique representative of degree ≤ 7.

In characteristic 5, (Σ c_i t^i)^5 = Σ c_i t^{5i} for c_i ∈ F_5. Therefore, if t^{5^k} = P_k(t) with P_k = Σ c_i X^i, then P_{k+1} = Σ c_i B_i, where B_i is the residue of X^{5i} mod f. Coefficients below are listed from X^0 to X^7.

| i | B_i = X^{5i} mod f |
|---|---|
| 0 | 1 0 0 0 0 0 0 0 |
| 1 | 0 0 0 0 0 1 0 0 |
| 2 | 2 2 3 0 0 0 2 3 |
| 3 | 4 1 0 2 4 2 1 1 |
| 4 | 4 2 0 0 3 4 0 4 |
| 5 | 2 3 0 3 2 4 4 4 |
| 6 | 0 3 3 0 2 2 3 3 |
| 7 | 1 3 3 0 4 0 4 4 |

| k | P_k = t^{5^k} |
|---|---|
| 0 | 0 1 0 0 0 0 0 0 |
| 1 | 0 0 0 0 0 1 0 0 |
| 2 | 2 3 0 3 2 4 4 4 |
| 3 | 4 3 4 3 0 1 2 0 |
| 4 | 1 0 3 4 3 2 1 0 |
| 5 | 4 0 2 4 1 0 1 1 |
| 6 | 4 1 2 3 0 4 0 1 |
| 7 | 4 2 4 3 4 3 2 4 |
| 8 | 0 1 0 0 0 0 0 0 |

Since P_8 = X, we get t^{5^8} = t, so f divides X^{5^8} − X in F_5[X], and hence in K[X].

In K[X], X^{|K|} − X = ∏_{a∈K} (X − a). The monic polynomial f divides this product of distinct linear factors, so by unique factorisation f is itself a product of 8 distinct linear factors over K. In particular there is θ ∈ K with f(θ) = 0. Irreducibility of f is not used here.

Lean: `fK_dvd` proves t^{5^k} = P_k(t) in AdjoinRoot(f) over K, one step at a time. Each step is an exact identity P_k(T)^5 − P_{k+1}(T) = A_k(T) f(T) + 5 B_k(T) in Z[T], checked by `linear_combination`. `exists_root` then uses `Polynomial.splits_X_pow_nat_card_sub_X` and `Splits.of_dvd`.

## 4. Irreducibility via the Frobenius orbit (supplement; not used by Lean)

Since f | X^{5^8} − X, f is squarefree, and each of its irreducible factors over F_5 has degree dividing 8.

Suppose f were reducible. Then every irreducible factor would have degree 1, 2 or 4, and so would divide X^{5^4} − X. Because the factors are distinct, f itself would divide X^{625} − X, which means P_4 = X. But P_4 = 1 + 3X^2 + 4X^3 + 3X^4 + 2X^5 + X^6 ≠ X.

Hence f is irreducible, and F_5[X]/(f) is a field with 5^8 elements. The Frobenius orbit of θ is {θ, θ^5, …, θ^{5^7}}, of exact length 8: P_k ≠ X for 1 ≤ k ≤ 7 and P_8 = X. As a cross-check, gcd(f, P_4 − X) = 1 (Rabin's test). This is confirmed by `diagnostic.py`, independently of the author's code.

## 5. Cube certificates

Put x = 2θ + 4θ^2 + θ^3. For each a ∈ F_5 the Lean module gives polynomials y_a and h_a of degree ≤ 7 such that, modulo (f, 5):

- y_a(T)^3 ≡ x(T) − a, and
- (x(T) − a) · h_a(T) ≡ 1.

Coefficients are listed from X^0 up:

| a | y_a | h_a |
|---|---|---|
| 0 | 0 4 3 3 2 3 0 0 | 3 2 2 0 4 4 4 3 |
| 1 | 3 4 4 4 1 1 0 4 | 2 3 3 0 0 3 4 3 |
| 2 | 4 4 3 4 4 3 1 2 | 2 1 2 0 2 3 2 3 |
| 3 | 2 1 0 4 0 0 4 0 | 2 4 2 4 0 1 1 0 |
| 4 | 0 0 1 2 2 4 0 3 | 1 0 1 2 2 2 1 0 |

Evaluating at θ gives x − a = y_a(θ)^3 and (x − a) · h_a(θ) = 1 in K. Hence x − a ≠ 0, so y_a(θ) ≠ 0, and x − a is a nonzero cube. Each identity is a single product of two polynomials of degree ≤ 7 reduced modulo f over F_5, which is checkable by hand or with a few lines of code.

**Why −1 is a cube.** For d = 3, −1 = (−1)^3. In general, q ≡ 1 (mod 2d) gives d | (q−1)/2, so −1 = g^{(q−1)/2} is a d-th power for any generator g of F_q^*. This is why GP(q,d) is undirected.

Consequently a − x = (−y_a(θ))^3 is also a nonzero cube.

Every w ∈ F_5^* satisfies w^4 = 1, so w = w^9 = (w^3)^3. Thus every nonzero element of F_5 is a cube in K.

Lean: `cube_0`…`cube_4`, `inv_0`…`inv_4`, `wit_sub_mem`, `small_sub_mem`.

## 6. The extension argument

F_5 is a clique, because differences of distinct elements are nonzero elements of F_5, which are cubes by Section 5. Since d | (q−1)/(p−1), this is also the Broere–Döman–Ridley observation as quoted by Yip [1, Theorem 1.3].

The vertex x lies outside F_5, since x − a ≠ 0 for every a. For every a ∈ F_5, both x − a and a − x are nonzero cubes. So F_5 ∪ {x} is a clique strictly containing F_5, and F_5 is not a maximal clique of GP(5^8, 3). This holds in every field K with 5^8 elements; θ is any root of f in K.

Taking (d, p, q) = (3, 5, 5^8), which satisfies every hypothesis with r = 1, refutes the conjecture. ∎

Lean: `not_maximal_of_card` and `yip_conjecture_false`, instantiated at `GaloisField 5 8`, whose cardinality is proved. The SimpleGraph form, `not_maximal_SG_of_card` and `yip_conjecture_SG_false`, uses `SimpleGraph.fromRel` and Mathlib's `Maximal`. For d = 3 the relation is already symmetric, and the proof supplies both directions explicitly.

## 7. Further consequences (ordinary proofs, NOT Lean-certified) and diagnostics

**Proposition A (a 25-clique).** V = F_5 + x F_5 is a clique of size 25, so ω(GP(5^8, 3)) ≥ 25.

*Proof.* Take distinct u = a + bx and v = a' + b'x.
- If b = b', then u − v = a − a' ∈ F_5^*, which is a cube.
- If b ≠ b', then u − v = (b − b')(x − c) with c = (a' − a)/(b − b') ∈ F_5. This is a product of two nonzero cubes, hence a nonzero cube.

|V| = 25 because x ∉ F_5. ∎

This is the two-dimensional clique predicted by Yip's lemma [1, Section 2].

**Proposition B (F_5 is a maximal subfield clique).** The subfields of K are F_5, F_25, F_625 and K. A subfield L is a clique iff L^* ⊂ (K^*)^3. Since L^* is the unique subgroup of order |L| − 1 of the cyclic group K^*, this holds iff 3 | (q − 1)/(|L| − 1). The quotients 16276, 626 and 1 are not divisible by 3, so only F_5 is a subfield clique. ∎

ALCO Theorem 1.2 [2] asserts: if d > 1, q^n ≡ 1 (mod 2d), q > (n−1)^2 and F_q is a maximal subfield clique of GP(q^n, d), then F_q is a maximal clique. Here the base field has q = 5, with n = 8 and d = 3. The hypothesis q > (n−1)^2 fails (5 ≤ 49), so the theorem is not contradicted. However, the ALCO remark "We conjecture that the condition q>(n−1)^2 in Theorem 1.2 can be dropped" is false by Proposition B and Section 6.

**Diagnostics (computational only; not premises):**
- **Exactly 960 extension vertices.** There are exactly 960 elements y ∈ K \ F_5 such that F_5 ∪ {y} is a clique. This count comes from a log-table search in this lane's `diagnostic.py`, and the source review found the same number independently. None of the 960 lies in F_625, consistent with Yip's SageMath verification for n ≤ 5, which covers GP(625, 3).
- **θ is primitive.** θ is a primitive element of K, and generators of F_25^* and F_625^* are non-cubes.
- **Author's sweep (not re-run here).** The author lane searched every admissible case with q ≤ 5 · 10^6 outside Theorem 1.2's range (26 fields, 219 cases) and found only this failure.
- **Outside Yip's checks.** The case n = 8 lies outside the reported checks (n ≤ 5, and n = 6 with q ≤ 17).
