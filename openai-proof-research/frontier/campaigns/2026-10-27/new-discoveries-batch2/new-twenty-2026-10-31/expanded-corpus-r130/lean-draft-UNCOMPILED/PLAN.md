# 342364 Lean plan (UNCOMPILED; no Lean, lake or leanchecker was run in this lane)

## Endpoint options (root chooses)

E1 (refutation only, smallest). This proves `fifteen_divisibility` and `conj61_equality_clause_false`.
E2 (full resolution). This adds `even_case` and the odd inequalities (the theorem in outputs/342364-proof.md).

## Statement correspondence

* `c m n` is literally the coefficient of x^n in (1/(1-x) · prod_{i>=0} 1/(1-x^{2^i}))^m. Truncating the product at i < n+1 does not change coefficient n. One lemma, `coeff_G_stable`, is needed: for N >= n+1, coeff n of (G N)^m equals coeff n of (G (n+1))^m, because geomStep (2^i) ≡ 1 mod X^{2^i} and 2^i > n.
* Valuations: ν₂(n) is `padicValNat 2 n` and ν₂(d) is `padicValInt 2 d`. Note that `padicValInt 2 0 = 0` in Mathlib. The even case therefore also states that the difference is nonzero.
* The source's "for infinitely many n ∈ N": N includes 0 in the source, but n = 0 gives difference 0, so restricting to n >= 1 is harmless. Root should confirm.

## Proof architecture (mirrors outputs/342364-proof.md)

Work with integer sequences rather than power-series division where possible.

1. Computable twin. Define `cRec m : ℕ → ℤ` by the recurrence from (1-x)^m C_m(x) = (1+x)^m C_m(x^2):
   cRec m n = sum_{j=1}^{min(m,n)} (-1)^{j+1} binom(m,j) cRec m (n-j) + sum_{j ≡ n (2), j <= min(m,n)} binom(m,j) cRec m ((n-j)/2).
   Prove `c = cRec` from the product identity G(x) = w · G(x^2) at truncation level, where w = (1+x)/(1-x) is realised as geomStep 1 * (1 + X).
2. The y-basis. For a polynomial F ∈ ℤ[Y], define seqOf m F n := sum_E F_E · sum_{i<=n} c_m(i) · binom(n-i-1, E-1), with the convention for E = 0. This is the x-coefficient of C^m(x) F(x/(1-x)).
3. Key identity (F2 + Lemma R): seqOf m (Y*(1+Y)*R) (2n) = seqOf m (Y*(1+Y)*Ttilde m R) n, where `Ttilde` is the explicit ℤ-linear map on monomials with binomial coefficients 4^i binom(·,·). This is the hardest formal step. Two routes:
   (a) Power-series route: prove U_2(C^m F) = C^m T(F) in `PowerSeries ℤ` via the evenPart operator, with the Chebyshev expansions as polynomial identities checked by `ring`-style induction on e.
   (b) Sequence route: prove the identity for the basis polynomials y^E·y(1+y) by strong induction on n, using the recurrence for c_m and binomial identities.
4. Base data: d_0 = A_2 - 1 = y(1+y) r_0. For E1 (m = 15) this is one explicit polynomial r_0 of degree 28. Its 29 integer coefficients can be checked by `decide`/`norm_num`, giving ω(r_0) >= 7 and ω(Ttilde r_0) >= 8. These are concrete arithmetic facts; logs/reduced-m1-64-J6.log has omega_seq [7, 11, 12, 17, 18, 24] for m = 15.
5. Weight lemma W: if ω(R) >= w then ω(Ttilde R) >= w + 1. This is a finite per-monomial estimate using 2^{2i} | 4^i·binom and bitlen(e+i) <= bitlen(e) + bitlen(i). Formalise it with `Nat.log 2` and `Nat.size`.
6. Induction on j gives r_j ∈ 2^{7+j} ℤ[Y], which yields divisibility at n = 2^j·o.
7. `conj61_equality_clause_false` follows: the set is in fact empty.

For E2, additionally formalise the ρ = 8 U_{k-1}^2 factorisation (Pell identity T_{2k} - 1 = 2(w^2-1)U_{k-1}^2), the invariant I(R,v), the parity C^m ≡ 1 (mod 2), and the odd-m interpolation facts. Those are better proved as polynomial identities in t than by interpolation.

## Risk notes

* Step 3 is the main cost. All other steps are finite or elementary.
* No `native_decide` should be used. The degree-28 coefficient checks are small enough for `decide` over ℤ with `Int.emod`/`Nat` lemmas, or for `norm_num`.
