# 338887 — statement correspondence and Lean plan (for root / Sol; nothing was compiled in this lane)

## Endpoint
`formal/ChanLevine338887.lean`, theorem `chan_levine_conjecture_8_3`:

  ∀ n m, 3 ≤ n → 1 ≤ m → ∀ i j : ZMod n, gcd(gcd n m, i.val) = gcd(gcd n m, j.val) → recCount n m i = recCount n m j.

## Correspondence
| Source (arXiv:1804.03322v2) | Lean |
|---|---|
| bidirected cycle C_n, vertices v_k, k ∈ Z_n | `ZMod n` |
| rotor state q(v_k) ∈ {(v_k,v_{k+1}), (v_k,v_{k−1})} | `Rotor n := ZMod n → Bool` (`true` = clockwise) |
| wt(v_k, v_{k−1}) = 1, otherwise 0 | the `filter (q k = false)` term of `weight` |
| wt(x.q) = Σ x(v_k)·k + wt(q) mod n | `weight` |
| recurrent configuration (Def. 5.2) | `Recurrent`, via the cycle test (Thm 7.4 / Thm 1.3): x ≥ 0 is built into ℕ, local recurrence is automatic, and the directed cycles of a rotor digraph on C_n (n ≥ 3) are facing pairs plus the two Hamiltonian cycles |
| r(C_{n,m,i}) | `recCount n m i`, via Lemma 5.19 and §8.3 (weight and chip invariance plus uniqueness of C_{n,m,i}) |
| gcd(n, m, i) | `Nat.gcd (Nat.gcd n m) i.val` |

Root decision needed: the source-theorem bridge from abelian-network recurrent components to the count is not
formalized. The Lean statement is the count form. A fully literal formalization would need the trajectory-digraph
semantics and the cycle test, which is a much larger project. Precedent from earlier accepted packets, where
source characterizations were taken as definitions, should be checked.

## Placeholders to discharge (estimated size)
1. `recCount_add_m` (about 80 lines): `Finset.card_bij` with the rotation, plus reindexing a sum over `ZMod n`.
2. `orbit` (about 60–120 lines): `ZMod.unitsMap_surjective` and gcd bookkeeping.
3. `recCount_mul_unit` (about 150 lines): `ZMod.dft` injectivity (`ZMod.dft_dft` or `ZMod.dft_injective` in
   Mathlib.Analysis.Fourier.ZMod). Use 𝓕 N(k) = W(ζ_n^{−k}), and note that ζ_n^{−k} and ζ_n^{−uk} have the same
   order. This step uses `W_primitive`.
4. `W_primitive` (the main effort, about 600–1200 lines):
   a. Truncation: W_m(ζ) equals the t^m coefficient of a finite polynomial identity. Work modulo t^{m+1}, or
      over `PowerSeries ℂ` with `x` bounded by m.
   b. Inclusion–exclusion over facing pairs (disjointness lemma), giving the matching sum.
   c. Domino transfer-matrix trace equals the matching sum (closed-walk bijection on `Fin 2` states). Alternatively,
      define everything by the trace and prove the matching expansion by induction on a path, then close the cycle.
   d. Period reduction Π_{k<n} X_k = (Π_{k<e} X_k)^{n/e}, and Π_{k<e}(1 − tζ^k) = 1 − t^e
      (`IsPrimitiveRoot.prod_one_sub_mul`-style lemma; `Polynomial.X_pow_sub_one_eq_prod`).
   e. Degree ≤ e plus invariance under t ↦ ζt forces the trace to be 2 + q_e t^e; the constant and top
      coefficients are computed exactly.
   f. Cayley–Hamilton for 2×2 matrices (`Matrix.trace_pow`-style recurrence, or a direct induction), giving the
      Lucas recurrence.

Before investing, the size suggests checking whether a lighter route exists. Steps (a)–(c) could be replaced by a
direct DP-style transfer matrix over (rotor, chips) with polynomial weights.
