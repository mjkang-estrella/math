# Proof of T179A

Author work of fresh-arithmetic-discovery-r72. This is a candidate proof; no
independent gate has run. Statement: see `scope-freeze.md` (frozen, SHA-256 in
`scope-freeze.sha256`). Stipulated inputs are from family 179 at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`preprints/The-circulant-Hadamard-conjecture-September-23-2026/build/sections/`.
"Source" below always means those files; labels are the literal TeX labels.

Notation. ω = e^{2πi/3}. For a finite abelian group G and a subring R of ℂ stable
under complex conjugation, R[G] is the group ring and
(Σ a_g g)^* = Σ ā_g g^{-1}. J_G = Σ_{g∈G} g. A character evaluation
χ : R[G] → ℂ satisfies χ(f^*) = \overline{χ(f)}.

Throughout, "unit coefficients" means: in part (a) every coefficient lies in
U_4 = {1, i, −1, −i}; in part (b) in U_3 = {1, ω, ω²}.

## 0. Translation into group rings

Let H be circulant of order n with first row (h_0,…,h_{n−1}), H_{jk} = h_{k−j}.
Put h = Σ_k h_k X^k in ℂ[C_n], X a generator. The coefficient of X^a in hh^*
is Σ_k h_k \overline{h_{k−a}} = (H H^*)_{0,a}, and by circulancy
(HH^*)_{j,j+a} = (HH^*)_{0,a}. Hence

  HH^* = n I_n  ⟺  hh^* = n  (scalar in ℂ[C_n]).                       (0.1)

## 1. The elementary residue classes

**Lemma 1.1.** (a) If n > 1 and a circulant complex Hadamard matrix of order n
with entries in U_4 exists, then n is even. (b) If n > 1 and one with entries
in U_3 exists, then 3 | n.

*Proof.* Take a = 1 in (0.1): Σ_{k} h_k \overline{h_{k−1}} = 0 is a sum of n
elements of U_q (the alphabet is a group). (a) Each element of U_4 is ≡ 1 mod
(1+i) in ℤ[i], because i − 1 = i(1+i) and −1 − 1 = −(1+i)(1−i). So the sum is
≡ n mod (1+i). Zero forces (1+i) | n in ℤ[i], i.e. 2 | n. (b) Each element of
U_3 is ≡ 1 mod λ = 1 − ω, since ω − 1 = −λ and ω² − 1 = (ω − 1)(ω + 1). So
n ≡ 0 mod λ, and λℤ[ω] ∩ ℤ = 3ℤ because λ\barλ = 3 and 3 is the only rational
prime below λ. ∎

**Existence at the listed orders.** n = 1: H = (1). (a) n = 2: first row (1, i),
H = [[1, i], [i, 1]], HH^* = 2I. (b) n = 3: first row (1, 1, ω); the rows are
(1,1,ω), (ω,1,1), (1,ω,1), and ⟨row0,row1⟩ = ω² + 1 + ω = 0,
⟨row0,row2⟩ = 1 + ω² + ω = 0. (Also found by the exhaustive controls in
`controls.json`.)

By Lemma 1.1, T179A reduces to:

**Theorem 1.2.** Let q ∈ {2, 3}, let m > 1 be an integer coprime to q, and put
n = qm. (a) For q = 2 (so m is odd) there is no h ∈ ℤ[i][C_n] with coefficients in
U_4 and hh^* = n. (b) For q = 3 there is no h ∈ ℤ[ω][C_n] with coefficients in
U_3 and hh^* = n.

Indeed in (a), 4 ∤ n and n > 2 even means n = 2m with m odd, m > 1; in (b),
9 ∤ n, n > 3 and 3 | n means n = 3m with 3 ∤ m, m > 1.

## 2. Setup and normalization

Fix q, m, n as in Theorem 1.2 and suppose h exists. Let O_0 = ℤ[i] if q = 2 and
O_0 = ℤ[ω] if q = 3, and let ϖ = 1 + i, resp. ϖ = λ = 1 − ω. Then
ϖ\barϖ = q, every alphabet letter is ≡ 1 mod ϖ (proof of Lemma 1.1), and
μ_q ⊂ U_q ⊂ O_0^×.

Since gcd(q, m) = 1, C_n = T × P with T = C_q (generator Z) and P = C_m.
Reindexing the coefficients,

  h = Σ_{t=0}^{q−1} Z^t H_t,  H_t ∈ O_0[P] with all coefficients in U_q.   (2.1)

For η ∈ μ_q the partial evaluation Z ↦ η is a ring homomorphism
O_0[T × P] → O_0[P] commuting with * (because η^{-1} = \barη). Put
h_η = Σ_t η^t H_t. Then h_η h_η^* = n.

**Lemma 2.1 (automatic normalization).** For every η ∈ μ_q,
x_η := h_η / ϖ lies in O_0[P] and x_η x_η^* = m.

*Proof.* A coefficient of h_η has the form Σ_{t<q} η^t u_t with u_t ∈ U_q.
Each summand is an alphabet letter times a q-th root of unity, hence ≡ 1 mod ϖ
(μ_2 = {±1} ⊂ U_4; μ_3 = U_3). So the coefficient is ≡ q ≡ 0 mod ϖ. The norm
follows from h_η h_η^* = n and ϖ\barϖ = q, since * acts on the scalar ϖ by
conjugation. ∎ (Finite exact check: `a_partial_eval_divisible`,
`b_partial_eval_divisible` in `exact-check-results.json`.)

## 3. The alternating product for C_m and scalar m

This section re-runs the source's Proposition `prop:alternating` for the group
P = C_m and scalar m, over the coefficient ring O_0. The source states it for
P = C_{u²}, scalar u², O_0 = ℤ[i]. Every step is checked here; the inputs used
are the source's Lemma `lem:local-ring`, Lemma `lem:comparison` and Lemma
`lem:torsion`, applied under their stated hypotheses.

Let I be the (nonempty) set of primes dividing m. For p ∈ I let p^{e_p} be the
order of the p-component P_p of P; since P is cyclic of order m, P_p is cyclic and

  e_p = v_p(m).                                                       (3.1)

Fix a generator X_p of P_p and a primitive p-th root of unity ρ_p (ρ_2 = −1). For
S ⊆ I let χ_S be the character of P with χ_S(X_p) = ρ_p for p ∈ S and = 1 for
p ∉ S, and for x ∈ O_0[P] put x_S = χ_S(x). All x_S lie in

  B = O_0[ρ_p : p ∈ I],                                               (3.2)

a ring generated over ℤ by finitely many roots of unity. Put ε_S = (−1)^{|S|}.

**Proposition 3.1.** Let x ∈ O_0[P] satisfy xx^* = m. Then
Δ(x) = Π_{S⊆I} x_S^{ε_S} belongs to B, is a root of unity, and for every p ∈ I
its order is a power of p. In particular its order is prime to q.

*Proof.* Character evaluation gives x_S \overline{x_S} = m, so each x_S ≠ 0 and Δ(x)
is a well-defined element of Frac(B).

*Primes above p ∈ I.* Fix p ∈ I and a maximal ideal 𝔪 of B containing p. Let
A_0 = O_0[ρ_r : r ∈ I∖{p}]. With c = 4 if q = 2 and c = 3 if q = 3, A_0 = ℤ[η] for
η = ζ_c · Π_{r∈I∖{p}} ρ_r, a primitive L-th root of unity with
L = c Π_{r ∈ I∖{p}} r (the factors have pairwise coprime orders). The hypothesis
of `lem:local-ring` is p ∤ L. This holds: in (a) p is odd and c = 4; in (b)
p ≠ 3 = c (p = 2 is allowed when m is even). Let 𝔪_0 = 𝔪 ∩ A_0 (a prime of A_0
containing p, hence maximal because A_0/pA_0 is a product of fields, as in that
lemma's proof) and A = (A_0)_{𝔪_0}.

Let S ⊆ I with p ∉ S. Write P = P_p × P' and let φ_S : O_0[P] → A_0[P_p] be the
ring homomorphism sending g' ∈ P' to χ_S(g') and fixing P_p. Then
F = φ_S(x), K = φ_S(x^*) ∈ A_0[C_{p^{e_p}}] (the image of x^* has conjugated O_0-
coefficients and inverted roots ρ_r, both in A_0), and

  FK = φ_S(xx^*) = m = p^{e_p} b,  b = m / p^{e_p} ∈ ℤ, p ∤ b,

by (3.1). After localization b ∈ A^×, and e_p ≥ 1. These are exactly the
hypotheses of `lem:comparison`, which gives that F(ρ_p)/F(1) is a unit of
A[ρ_p] with residue 1. Now F(1) = x_S and F(ρ_p) = x_{S∪{p}}. Every element of
A_0 ∖ 𝔪_0 is outside 𝔪, so A[ρ_p] ⊂ B_𝔪; and ρ_p − 1 ∈ 𝔪B_𝔪 because the residue
field has characteristic p and (ρ_p − 1)^p ≡ ρ_p^p − 1 = 0 (for p = 2,
ρ_2 − 1 = −2). Hence x_{S∪{p}}/x_S ∈ B_𝔪^× has residue 1. Since
ε_{S∪{p}} = −ε_S,

  Δ(x) = Π_{S⊆I, p∉S} (x_S / x_{S∪{p}})^{ε_S},                          (3.3)

so Δ(x) ∈ B_𝔪^× with residue 1 at 𝔪.

*Other maximal ideals.* If 𝔪 contains no prime of I, then m ∈ B_𝔪^×, so every
x_S ∈ B_𝔪^× (x_S \overline{x_S} = m with \overline{x_S} ∈ B), and Δ(x) ∈ B_𝔪.

*Integrality.* An element of Frac(B) lying in B_𝔪 for every maximal 𝔪 lies in B
(the ideal {b : bz ∈ B} is not contained in any maximal ideal; this is the
argument in the source's proof). So Δ(x) ∈ B.

*Root of unity.* Every unital σ : B → ℂ sends the generators to roots of unity
and commutes with conjugation on their integer polynomials, so
|σ(x_S)|² = m for all S. Writing Δ = P_+/P_− with P_± ∈ B the products over
ε_S = ±1, σ(P_−) ≠ 0 and |σ(Δ)| = m^{(Σ_S ε_S)/2} = 1 because
Σ_S ε_S = (1 − 1)^{|I|} = 0 (I ≠ ∅). By `lem:torsion`(i) (Kronecker), Δ(x) is a
root of unity.

*Order.* For p ∈ I a maximal ideal of B containing p exists (B is free of finite
positive rank over ℤ, so B/pB ≠ 0). There Δ(x) has residue 1, so by
`lem:torsion`(ii) its order is a power of p. As I ∌ q, the order is prime to q. ∎

## 4. The contradiction

Let 𝔪 be a maximal ideal of B containing q (exists since B/qB ≠ 0), O = B_𝔪,
𝔫 = 𝔪O, k = O/𝔫 (characteristic q). For every η ∈ μ_q and S ⊆ I,
(x_η)_S \overline{(x_η)_S} = m with q ∤ m, so (x_η)_S ∈ O^×. Also ϖ ∈ 𝔫: in (a)
(1+i)² = 2i, in (b) λ² = −3ω, and 𝔫 is prime; and ϖ ≠ 0 in the domain O.
We use the source's Lemma `lem:first-order`: for 0 ≠ t ∈ 𝔫, 1 + tO is a subgroup
of O^× and λ_t(1 + tL) = L mod 𝔫 is a homomorphism to (k, +).

### 4(a). Fourth roots (q = 2, m odd)

Here c := x_1 = (H_0 + H_1)/(1+i) and d := x_{−1} = (H_0 − H_1)/(1+i). Then

  d − c = −2H_1/(1+i) = −(1−i) H_1.                                   (4.1)

Put R = Δ(d)/Δ(c). By Proposition 3.1, R is a root of unity of odd order
(each factor has order a power of an odd prime of I, or 1). For S ⊆ I let
r_S = d_S / c_S ∈ O^×. By (4.1),

  r_S = 1 + (1−i) L_S,  L_S = −(H_1)_S / c_S ∈ O,                       (4.2)

so r_S ∈ 1 + (1−i)O has residue 1, and R = Π_S r_S^{ε_S} has residue 1. By
`lem:torsion`(ii) in residue characteristic 2, the order of R is a power of 2;
being odd, R = 1. Applying λ_{1−i} (1 − i ∈ 𝔫, ≠ 0) to Π_S r_S^{ε_S} = 1,

  Σ_{S⊆I} ε_S (H_1)_S / c_S ≡ 0  (mod 𝔫).                              (4.3)

Every coefficient of H_1 is ≡ 1 mod (1+i), so H_1 = J_P + (1+i)V with
V ∈ ℤ[i][P], and (H_1)_S ≡ (J_P)_S mod 𝔫. For S ≠ ∅, χ_S is nontrivial and
(J_P)_S = 0 (choose z with χ_S(z) ≠ 1; then (χ_S(z) − 1)(J_P)_S = 0 in the domain
B). For S = ∅, (J_P)_∅ = m and ε_∅ = 1. So (4.3) becomes m / c_∅ ≡ 0 mod 𝔫. But
m and c_∅ are units of O. Contradiction. This proves Theorem 1.2(a).

(Exact coefficientwise check of (4.1): `a_difference_identity`.)

### 4(b). Cube roots (q = 3, 3 ∤ m)

Here x_η = (H_0 + ηH_1 + η²H_2)/λ for η ∈ {1, ω, ω²}. Since (ω − 1)/λ = −1 and
(ω² − 1)/λ = −(ω + 1) = ω²,

  x_ω − x_1 = −H_1 + ω² H_2,   x_{ω²} − x_1 = ω² H_1 − H_2.              (4.4)

Every coefficient on the right of (4.4) is −u + ω²u' or ω²u − u' with
u, u' ∈ U_3, hence ≡ 0 mod λ. So x_ω − x_1 = λM and x_{ω²} − x_1 = λM' with
M, M' ∈ ℤ[ω][P], and, from (4.4),

  λ(M + M') = (ω² − 1)(H_1 + H_2) = λ ω² (H_1 + H_2),
  hence M + M' = ω² (H_1 + H_2)                                       (4.5)

(cancellation of λ is valid in the free ℤ[ω]-module ℤ[ω][P]). Every
coefficient of H_1 + H_2 is a sum of two letters, ≡ 2 ≡ −1 mod λ (as 3 ≡ 0), and
ω² ≡ 1. Therefore

  M + M' ≡ −J_P  (mod λ ℤ[ω][P]).                                     (4.6)

Put R_1 = Δ(x_ω)/Δ(x_1) and R_2 = Δ(x_{ω²})/Δ(x_1). By Proposition 3.1 both are
roots of unity of order prime to 3. For S ⊆ I put
r_{1,S} = (x_ω)_S/(x_1)_S = 1 + λ M_S/(x_1)_S and
r_{2,S} = (x_{ω²})_S/(x_1)_S = 1 + λ M'_S/(x_1)_S, both in 1 + λO. Hence R_1 and R_2
have residue 1; in residue characteristic 3 their orders are powers of 3
(`lem:torsion`(ii)); being prime to 3, R_1 = R_2 = 1. Applying λ_λ to both
products and adding,

  Σ_{S⊆I} ε_S (M + M')_S / (x_1)_S ≡ 0  (mod 𝔫).                        (4.7)

By (4.6), (M + M')_S ≡ −(J_P)_S mod 𝔫, which vanishes for S ≠ ∅ and equals −m
for S = ∅. So (4.7) says m/(x_1)_∅ ≡ 0 mod 𝔫, contradicting m, (x_1)_∅ ∈ O^×.
This proves Theorem 1.2(b), and with §1, T179A. ∎

(Exact coefficientwise checks of (4.4)–(4.6): `b_quotients`,
`b_difference_identities`, `b_divisible_by_lambda`,
`b_first_order_sum_identity`, `b_first_order_sum_congruent_minus_one`.)

## 5. Where each hypothesis enters

* m > 1: makes I nonempty, needed for Σ ε_S = 0 (Kronecker step) and for the
  order restriction. For m = 1 the orders n = 2 and n = 3 do exist.
* gcd(m, q) = 1: gives the coprime splitting C_n = C_q × C_m, makes x_η 𝔪-units,
  and ensures p ∤ L in `lem:local-ring` for every p ∈ I (the coefficient ring
  O_0 is generated by a root of unity of order 4, resp. 3).
* P cyclic: gives (3.1), the exact match between the scalar valuation and the
  cyclic exponent that `lem:comparison` requires (see the source's
  `rem:exponent` for failure otherwise).
* Alphabet: used only through "every letter is ≡ 1 mod ϖ" and μ_q ⊆ alphabet.
  For other alphabets or a larger q-part Lemma 2.1 fails (see `barriers.md`).

## 6. Paid versus unpaid operations

Paid by the stipulated source (used under its stated hypotheses):
`lem:local-ring`, `lem:comparison`, `lem:torsion`, `lem:first-order`, the
integrality-by-localizations argument and the overall architecture of
`prop:alternating` and of the final first-order contradiction in
`contradiction.tex` (two ratio families, odd/prime-to-ℓ torsion with residue 1,
linearization, isolation of J).

New in this proof: Lemma 1.1 (elementary; classical in spirit), Lemma 2.1
(automatic ϖ-normalization for the two alphabets), the re-run of
`prop:alternating` for C_m with arbitrary m (not a square) and for O_0 = ℤ[ω]
including p = 2, the identity (4.1) with a single ratio family in (a), and the
identities (4.4)–(4.6) in (b), whose sum isolates −J. These are short. Whether
they constitute a substantial contribution is for the separate gate; the
author's own expectation is recorded in `scope-freeze.md` and
`primary-comparison.md`.

Original prose: Myeongjin Kang, CC BY 4.0.
