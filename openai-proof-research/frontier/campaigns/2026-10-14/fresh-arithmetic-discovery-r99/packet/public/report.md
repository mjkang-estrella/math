# Arithmetic r99 report: family 164 in positive characteristic

Runner: Factory Droid / claude-opus-5-5 / high. Root:
`frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r99/`.
Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Outcome

Full author-proof nominee at the unchanged frozen scope. The scope was frozen
before proof development (`scope-freeze.md`, SHA-256
`2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7`,
2026-10-20T17:20:23Z); the proof is `proof.md`. This report assigns no
correctness, contribution, acceptance or count. Those reviews are separate.

**Theorem F.** For every infinite field `K` (any characteristic), all
`r, n ≥ 1` and every `χ: K^x → [r]`, there are pairwise distinct
`x_1,...,x_n ∈ K^x` whose nonempty subset sums are all nonzero and such that
`χ` is constant on all nonempty subset sums and subset products.

**Corollary G.** For every prime `p` and `r, n ≥ 1` there is `d` such that
the same holds in `F_{p^m}` for every `m` divisible by `d`.

The new case is positive characteristic, in particular small characteristic
(for example `F_2(t)` and the algebraic closure of `F_2`).

## Strongest integrated known reduction, and what it leaves

1. Characteristic 0: Alweiss (arXiv:2307.08901v6, Theorem 1.3) over `Q`
   restricts to every field containing `Q`. Distinctness comes from Hunter's
   `C(q) ≠ C(2q)` device (arXiv:2308.10749v1, Remark 1.1).
2. Large characteristic: the first-order compactness argument of Bowen–Sabok
   (arXiv:2210.12290v1, §4.3, Corollary 1.2), applied to Alweiss's theorem,
   gives every field of characteristic greater than some `p_0(r,n)`.
3. The pinned source (family 164) proves the statement over `N`. Its
   Prediction/Alignment machinery uses nilsequences on integer intervals and
   does not transfer to characteristic `p`. Structural r130 recorded that a
   positive-characteristic version "would need the whole nilsequence
   apparatus over function fields".

What is left by 1–3: fields of characteristic at most `p_0(r,n)`, i.e. a fixed
small characteristic with `r` or `n` large. Alweiss's text says field versions
follow from `Q` by compactness, but the compactness argument actually written
(Bowen–Sabok) reaches only large characteristic. Hunter's exposition uses
characteristic 0 explicitly ("D is finite (since N ⊂ Z has characteristic
zero)", proof of Lemma 6.1). Kousek (arXiv:2407.03304v1) treats
characteristic-0 density patterns and finite-field `{x, p(x)+y, xy}`.

## The operation used

- Replace Alweiss's Theorem 2.4 (integer polynomial van der Waerden, scaled to
  `Q`) by Bergelson–Leibman Corollary 7.11 (Annals 150; arXiv:math/9907201v1),
  which holds for any infinite ring. The colouring is pulled back to `K^E`
  along `q ↦ (x_n + Σ q_e x^S/x^T) x^U`, and the polynomial
  `P(w_0, w) = (w_e w_0^{d_e − 1})_e` with configuration
  `F = {(1, ℓ) : ℓ ∈ L^E}` gives exactly the shifts `ℓ_e k^{d_e}`.
- Replace Alweiss's height bound `s(·) ≤ M` by finite sets of multipliers and
  coefficients chosen backward. Topological compactness of colourings of
  `K^E` (K countable WLOG) gives a finite set `Φ` of admissible `(u, k)`
  independent of the variables. Hunter's characteristic-0 finiteness step is
  not needed.
- Nondegeneracy without order or size: isolate `0` as its own colour so all
  variables stay nonzero (`x_1` is only multiplied by nonzero `k`, and
  `χ(x_i + x_1) = χ(x_i)`); distinctness by `2X = 0` in characteristic 2 and
  by a 3-colouring `ψ` with `ψ(2z) ≠ ψ(z)` otherwise.
- Steps II–IV of Alweiss §5 (Ramsey and Folkman), as in the pinned source's
  `lem:chain-selection`, are characteristic-free.

All update identities are proved in `proof.md` Lemma 4. They were also checked
by random evaluation over `F_2, F_3, F_5`, two large prime fields and
`GF(2^8)` (`code/identity_check.py`, PASS). That check is not a proof.

## Honest risk statement

The proof is a transport of Alweiss's argument. The steps that change are the
recurrence input, the finite-set bookkeeping and the nondegeneracy argument.
A contribution reviewer may judge this routine; this report does not argue
the point either way. Novelty is project-level and limited to the searches in
`reading-limits.md`. Bergelson–Leibman–McCutcheon (2005) and the
function-field Ramsey literature were not read; a published
characteristic-`p` statement may exist.

## Not claimed

No bounds; no Corollary G for all large `m` (for example `F_{2^m}` with `m`
prime is not covered); no infinite, density, read-once or
sums-of-disjoint-products versions; no separation conditions.

## Files

`proof.md` (full proof), `scope-freeze.md` (frozen bytes, copy),
`prefreeze-feasibility.md` (pre-freeze calculations, copy of the root note),
`screens.md`, `reading-limits.md`, registers, `RIGHTS.md`, `reproduction.md`,
`status.json`; code in `../code/`.
