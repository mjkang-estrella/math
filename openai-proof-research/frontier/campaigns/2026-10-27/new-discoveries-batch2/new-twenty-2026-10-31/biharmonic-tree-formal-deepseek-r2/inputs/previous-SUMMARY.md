# SUMMARY — MathDB 352303, lane biharmonic-tree-formal-deepseek-r1

Credit 0. Campaign 58 of 80 unchanged. Acceptance is root-only; nothing here is claimed as credit.

## What is kernel-checked (green)

Four modules are green: compile exit 0 **and** `leanchecker` exit 0, with an audit module.

| module | compile label | kernel label | content |
|---|---|---|---|
| `BiHBase` | `base03` | `basecheck01` | literal `BH` via `SimpleGraph.lapMatrix` and `Matrix.IsHermitian.eigenvalues`; exactly one zero eigenvalue for a connected graph; star/path graphs |
| `BiHTrace` | `trace06` | `tracecheck01` | real spectral theorem, trace of inverse and inverse-squared via eigenvalues |
| `BiHBridge` | `bridge04` | `bridgecheck01` | `BH(G) = n * tr((M')^2)` from `L = B Bᵀ`, `Bᵀ 1 = 0`, `M = Bᵀ B` invertible, `ker L` = constants |
| `BiHAudit` | `audit01` | `auditcheck01` | `#print axioms` for every theorem above |

The audit shows only `propext`, `Classical.choice`, `Quot.sound` for all eleven audited theorems.

Main statements (verbatim from the sources):

* `BiH.bh G = (Fintype.card V : ℝ) * ∑ i : V, if lapEigs G i = 0 then 0 else (lapEigs G i)⁻¹ ^ 2`
* `BiH.card_zero_eigs_of_connected (hG : G.Connected) : (univ.filter (lapEigs G · = 0)).card = 1`
* `BiH.trace_inv_sq_eq_sum_inv_sq (hdet : A.det ≠ 0) : (A⁻¹ * A⁻¹).trace = ∑ i, ((hA.eigenvalues i)⁻¹) ^ 2`
* `BiH.bh_eq_card_mul_trace_inv_sq : bh G = (Fintype.card V : ℝ) * (M' * M').trace`

This pays step 1 of the ROUTE in full, and the reusable half of step 2: the passage from the
literal eigenvalue definition of `BH` to a trace of an inverse squared matrix, given any
factorization of the Laplacian with the stated structural facts.

## What is unpaid

* **BiHFormula** — the edge-pair formula `BH(T) = N(T)/n` for trees. Needs (a) the oriented
  vertex–edge incidence matrix `B` (mathlib's `IncMatrix.lean` has only the unoriented 0/1 matrix
  and lists the oriented version as a TODO), (b) the entrywise identity `lapMatrix ℝ G = B * Bᵀ`,
  (c) `Bᵀ *ᵥ 1 = 0`, (d) invertibility of `M = Bᵀ * B` via positive definiteness
  (`xᵀ M x = ‖B x‖² > 0` for `x ≠ 0`, by leaf-peeling induction on the tree), (e) `ker L` =
  constant vectors, and (f) the explicit inverse `(M⁻¹)_{ef} = |A_e ∩ A_f| − a_e a_f / n`, which
  turns the bridge into `BH(T) = N(T)/n` with
  `N(T) = ∑_e [a_e(n−a_e)]² + 2 ∑_{{e,f}} (|C_e||C_f|)²`.
* **BiHLower** — `BH(K_{1,n−1}) ≤ BH(T)`, equality iff `T` is a star, from `a_e(n−a_e) ≥ n−1`
  (equality iff pendant) and `|C_e||C_f| ≥ 1` termwise in `N(T)`.
* **BiHShift / BiHUpper** — the pendant-path shift identity
  `N(T') − N(T) = (r−1)(pq/3)[ r(2p²+2q²+3pq+3p+3q+2) + 2pq(p+q) + 3pq + p + q ] + 2S pq(p+q+1) > 0`
  and `BH(T) ≤ BH(P_n)`, equality iff `T` is a path.
* **BiHEndpoint** — the literal theorem for every `n ≥ 5`, every finite `V` with `|V| = n` and
  every tree `G` on `V`, with `SimpleGraph.Iso` equality clauses on both sides. It has no added
  premise and is not stated anywhere in this lane yet, because it depends on all of the above.

## Route for a later lane

1. Add `BiHFormula`. The cheapest entry point is the oriented incidence matrix built from
   `Classical.choose` of `e ∈ G.edgeSet`, then the entrywise computation
   `(B Bᵀ)_{ab} = deg a` (a = b), `−1` (adjacent), `0` otherwise; this matches `lapMatrix` exactly.
2. `M = Bᵀ B` is positive definite on edge space: `xᵀ M x = ∑_e (x_h(e) − x_t(e))²`, and `B x = 0`
   forces `x = 0` by peeling a leaf. Positive definiteness gives invertibility directly, without
   any determinant computation. Supply `M' = M⁻¹` to `BiH.bh_eq_card_mul_trace_inv_sq`.
3. For the explicit inverse, use the reviewer's construction: `x_e = 1_{A_e} − (a_e/n)·1`,
   `Bᵀ x_e = e_e`, `X = B Y` with `Y = M⁻¹`, hence `(M⁻¹)_{ef} = ⟨x_e, x_f⟩`.
4. Then the two bounds are termwise (lower) and a shift (upper) as in `inputs/reviewer-PROOF.md`.

## State left behind

* No `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`; every failure kept with its true exit
  code in the corresponding `*.receipt.json` / `*.output.txt`.
* `results/352303.json` lists the four strict-green modules with source/olean hashes and labels.
* Probe modules `src/BiHProbe.lean`, `src/BiHProbe2.lean` are exploratory only and are not claimed.
