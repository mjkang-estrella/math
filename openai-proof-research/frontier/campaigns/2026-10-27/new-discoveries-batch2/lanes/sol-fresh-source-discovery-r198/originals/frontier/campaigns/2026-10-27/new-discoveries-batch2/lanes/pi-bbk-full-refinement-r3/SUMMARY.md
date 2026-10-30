# SUMMARY — pi-bbk-full-refinement-r3

**Date:** 2026-10-29 · **Agent:** pi (solo research sub-agent, task `bbk-full-refinement-r3`)

## Headline result

**Two new complete theorems** on BBK Conjecture 5.1 (arXiv:2601.04014, MathDB 372432, open with 0 solutions as of 2026-10-28):

> **Theorem A.** G_{4,n}(q) ⪰ 0 for all n ≥ 0.  **Theorem B.** G_{5,n}(q) ⪰ 0 for all n ≥ 0.

By the source's Lemma 5.3 symmetry (G_{k,n} = G_{n+1,k−1}, re-derived), this proves the conjecture on the entire region **{k ≤ 5} ∪ {n ≤ 4}**. The previously strongest facts were computational (source §5: k ≤ 200 by lcm-period evaluation; prior lanes: finite scans). Full write-up: **`PROOF-K4-K5.md`**. The conjecture itself remains **open for k ≥ 6 ∧ n ≥ 5**.

## Method (new)

Exact **quasi-polynomial certificate machines**: reduce the row to a denumerant sum (Lemma 1.2), prove an exact quadratic (k=4) / cubic (k=5) quasi-polynomial for the denumerant h of {1,3,5,7} with period 15 / 105, then verify nonnegativity regime-by-regime via Newton forward-difference certificates over **all** residue classes — 15 + 225 classes (k=4), 11025 + 2·11025 + 2×2·11025 classes (k=5). Every evaluation is exact rational arithmetic; the whole chain is cross-checked against directly computed series (27 009 comparisons, 0 mismatches). Key proved ingredients: h(15Q+r) = (15/2)Q² + ((2r+9)/2)Q + h(r) (Prop 2.2, full proof), a bivariate Newton-staircase sufficiency lemma, and a wedge/strip covering for growth regimes. The previously numerical h-superadditivity h(2u+3) ≥ h(u+2)+h(u) is now a proved lemma.

## Refutations of routes (rigorous)

- **Sub-object positivity is false:** (1−q⁷)/((1−q³)(1−q⁵)) has coefficient −1 at q⁷ (`run2`). No induction through sub-objects; Conjecture 5.4-style decompositions cannot hold sub-objectwise.
- **Divisor matching** (pair a ↦ b, b | a) fails for 229 (M,m) pairs with M < 4m+2 — a valid but strictly partial scheme, superseded.
- Weighted-CI Hilbert route: confirmed dead (prior lane's (n=4,k=6) counterexample stands).

## Boundary of the method

The identical machine at k = 6 (period 3465, degree-5 quasi-polynomial, 21-point staircase, ~13 regimes, ≈10¹⁰ exact ops) is **untested at scale**; a 225-class sample of the k=6 tail quadrant showed **0 failures** (`run9`) — no sign of obstruction, only a compute wall. No broad brute-force scan was used as a substitute for proof anywhere.

## Prior-art screen (closed first)

MathDB 372432 live: open, 0 solutions, 0 comments (`sources/mathdb-372432-live.json`). arXiv v1 still latest (`sources/bbk-v1.html`, sha256 5fa615bd…). All 5 Semantic Scholar citers' bodies re-checked: none address the G_{k,n} refinement (Chern–Wang proves F_{k,1} positivity only). Web search (exa, 3 queries): no new resolutions.

## Credit

Per task rules: pending review; this lane claims nothing. The theorems are restricted to the k=4/k=5 rows of the *same* conjecture — a partial advance on Conjecture 5.1, not a resolution of it, and not a formalization (Lean bridge is statements-only, honestly sorry-marked; see `BRIDGE-lean.md`).

## Artifacts

`PROOF-K4-K5.md` · `BRIDGE-lean.md` · `lean/Bridge.lean` · `checks/run1..9*.py` · `checks/logs/*.log` · `sources/*` · `discovery.md` · `progress.md` · `provenance.json`
