# Route limits beyond T179A

Author work. None of the statements below is nominated; they record why the
frozen theorem stops where it does and why the more ambitious targets
considered during screening were not frozen. "Proved" means a complete
argument is given here; "observed" means an exact computation of a specific
family, not an impossibility theorem.

## 1. Where automatic normalization holds

The source's method needs, for a factor C_q of the cyclic group and the
alphabet U, that every partial evaluation of the row at a character of C_q
be divisible by an element ϖ with ϖ\barϖ = q. Then the normalized elements have
scalar norm prime to q and the whole alternating-product machine runs.

Proved cases:

* U = {±1}, C_4: the source (sums of four signs are even).
* U = μ_4, C_2: Lemma 2.1 of `proof.md`.
* U = μ_3, C_3: Lemma 2.1 of `proof.md`.
* U = {±1}, C_2 × C_2: sums of four signs are even; the four Walsh partial
  evaluations have norm u² and three ratio families whose first-order terms
  sum to J modulo 2. This variant was already observed by
  fresh-structural-discovery-r60 (`screen179.md`), which judged it routine.
  It is not part of T179A.

Observed failures (exact checks in `exact-check-results.json`):

* U = μ_4, C_4 (orders 4m): a sum of four letters need not be divisible by 2
  (`limit_mu4_C4_sum_not_div_2`). Only division by 1+i is automatic, leaving
  norm 2m.
* U = μ_3, C_9 (orders 9m): a sum of nine cube roots need not be divisible by
  3 (`limit_mu3_C9_sum_not_div_3`).
* U = μ_p, C_p, p ≥ 5: divisibility by an element of norm p would require the
  coefficient sums to lie in (1−ζ_p)^{(p−1)/2}; sums of p letters are only
  guaranteed to lie in (1−ζ_p).
* U = μ_8, C_2: 1 + ζ_8 has (1−ζ_8)-adic valuation 1 while 1+i has valuation 2,
  so h_{±1}/(1+i) is not integral in general.

## 2. Norm identities alone do not force balance at a non-self-conjugate prime

When normalization is not automatic one would need, for every nontrivial odd
character χ, equal valuations of the evaluated row at the two primes
𝔓, \bar𝔓 above q interchanged by complex conjugation. Pure norm identities do
not supply this.

**Example 2.1 (exact).** In ℤ[C_7] with generator g, x = −1 + g + g² + g⁴
satisfies xx^* = 4 (`barrier_C7_norm_4`). Here {1,2,4} is the quadratic-residue
difference set, so x = D − 1 with DD^* = 2 + J and D + D^* = J − 1. For a
nontrivial character θ, x(θ) ∈ ℚ(√−7), where 2 = π\barπ with π = (1+√−7)/2.
A direct computation gives x(θ) = π² or \barπ², according to whether θ is in
one or the other ⟨2⟩-orbit; so x(θ) has valuations (2, 0) at (π, \barπ), while
x(1) = 2 has (1, 1). Every hypothesis of a norm-only balance argument holds,
and balance fails.

**Example 2.2 (exact).** In ℤ[i][C_9], x = (−9 + 12i) + 2J satisfies
xx^* = 225 (`barrier_C9_norm_225`), but x(1)/x(ρ) = (7 − 24i)/25 for a
character ρ of order 3 is not an algebraic integer. Thus for groups
C_4 × C_9 × K with |K| = 25 non-cyclic, a single-prime alternating product of
a projected element can fail to be integral at 5. This is the obstruction to
using the source for Lander-type statements (abelian groups with only some
Sylow subgroups cyclic). It is an algebraic obstruction to that route, not a
difference set.

## 3. Loss of the J-isolating identity for complex units with a C_4 factor

Suppose, to test the most favourable situation, that n = 4m (alphabet μ_4) and
that the partial evaluations h_ω, ω ∈ μ_4, are all divisible by 2 (which
holds, for example, if 2 is self-conjugate modulo m). Let c_ω = h_ω/2 (norm m).
The differences with residue-one ratios are

  c_{−1} − c_1 = −(H_1 + H_3),  c_{−i} − c_i = −i(H_1 − H_3),

each divisible by 1+i, while c_i − c_1 is not divisible by 1+i in general.
Observed (`limit_mu4_C4_first_order_terms_depend_only_on_u1_over_u3`): for all
256 choices of the four letters, the three normalized first-order quantities
reduce modulo 1+i to the indicator of {u_1/u_3 ∈ ±i}. They are independent of
u_0, u_2 and are never congruent to the all-ones element J. In the source the
contradiction comes from H_2 + iH_3 ≡ (1+i)J mod 2, which uses real signs; no
analogue appears among these families. This is a limit of the tested families,
not a proof that no other identity exists.

## 4. A proved inertia identity (method support only)

**Lemma 4.1.** Let n = 2^a m with a ≥ 1 and m > 1 odd, and let h ∈ ℤ[i][C_n]
have coefficients in μ_4 and hh^* = n. Write C_n = C_{2^a} × P and let ψ be a
character of C_{2^a} with ψ(C_{2^a}) ⊆ {±1}. Let \bar h be h with conjugated
coefficients (also such an element). Then Δ(\bar h_ψ) = Δ(h_ψ), where Δ is the
alternating product of §3 of `proof.md` taken over the primes of m.
Equivalently Δ(h_ψ) lies in ℚ(ρ_p : p | m).

*Proof.* Put y = h_ψ ∈ ℤ[i][P]; yy^* = n and v_p(n) = v_p(m) for odd p, so the
proof of Proposition 3.1 (which uses only the p-parts of the scalar) shows that
Δ(y) and Δ(\bar y) are units with residue 1 at every prime above every p | m,
and units at primes not above 2m. Let σ be the automorphism of
K = ℚ(i, ρ_p : p | m) fixing the ρ_p and sending i to −i. Then
σ(Δ(y)) = Δ(\bar y), because σ(χ_S(y)) = χ_S(\bar y). Every prime 𝔭 of
ℚ(ρ_p) above 2 is unramified, and 2 ramifies in ℚ(i), so 𝔭 has a unique prime
𝔓 of K above it, σ ∈ inertia, and σ acts trivially on O_K/𝔓. With the
uniformizer 1+i, σ(1+i)/(1+i) = −i ≡ 1 mod 𝔓, so σ(z)/z is a 𝔓-unit of
residue 1 for every z ∈ K^×. Thus Q = Δ(\bar y)/Δ(y) = σ(Δ(y))/Δ(y) is a unit
everywhere with |τ(Q)| = 1 for every embedding τ, hence a root of unity
(`lem:torsion`(i)); its residue is 1 above 2 and above an odd p | m, so its
order is both a power of 2 and a power of p, i.e. Q = 1. ∎

The lemma does not give 2-adic integrality of Δ(h_ψ) and does not settle any
order 2^a m with a ≥ 2; that is the open interface.

## 5. Status of the stronger targets

* Mow/Turyn conjecture over μ_4 (orders ≤ 16) and over μ_3 (orders ≤ 9):
  not frozen. After T179A, Turyn's 2-power exclusion and Ma–Ng's p^s exclusion
  (both literature inputs, not read here), the remaining orders are 2^a m
  (a ≥ 2, m > 1 odd) and 3^a m (a ≥ 2, m > 1, 3 ∤ m). Sections 1–3 show the
  missing operation: a 2-adic (resp. 3-adic) balance and J-isolation argument
  at non-self-conjugate primes. No plan for it exists here.
* Lander-type statements for real Menon–Hadamard difference sets: blocked by
  Example 2.2 at primes whose Sylow subgroup is not cyclic, unless a
  self-conjugacy hypothesis is added; such a hybrid was judged technical and
  was not frozen.

Original prose: Myeongjin Kang, CC BY 4.0.
