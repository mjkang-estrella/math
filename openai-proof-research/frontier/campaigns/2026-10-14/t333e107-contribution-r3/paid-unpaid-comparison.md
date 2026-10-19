# T333E107 r3: paid versus unpaid operations

This is a contribution comparison, conditional on correctness. **Classification:
TECHNICAL.** It is not a proof gate, an acceptance, or a count.

Source paths have the prefix
`preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/build/`
at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every label below was located and
read in the retained TeX. The retained files match their pinned Git blobs.

Allocation key:
- **PAID-S**: a stipulated source statement or proof operation.
- **ELEM**: an elementary classical step whose complete proof appears in the
  author note or in `review.md`. It receives no credit through any unread
  reference.
- **STD-TOP**: a standard topological input, identified but not read in a
  primary.
- **NEW-OBS**: the residual author observation.

| # | Author step (proof.md) | Allocation | Exact basis | Residual |
|---|---|---|---|---|
| 1 | Starting embedding M ↪ R³ ↪ S³ (§6) | STD-TOP | Handlebody realization of orientable closed surfaces; inverse stereographic projection | None. Its primary was not read and gets no operation credit. |
| 2 | Keep the embedding through spherical preparation (§6) | PAID-S + ELEM | `lem:spherical-preparation` (every ε < ε₀, constants independent of ε); proof of `lem:global-preparation` ("Fix a spherical immersion I and the uniform family"); C¹ openness (§2) | Choose the tolerance; no new estimate. |
| 3 | Metric decomposition, convex phases, transversality, finite list (Input 1) | PAID-S | `lem:global-preparation`, `eq:global-amplitudes`, `eq:cycle-identity` | None. Nothing changed. |
| 4 | Velocity plane P is complementary to dF(TM) (§3, (3.2)) | PAID-S | `lem:velocity-plane`: "tangential projections of Y,C are therefore independent … Projection from the normal plane to P is … an isomorphism". By orthogonal-complement duality, this is equivalent to P ∩ T = 0 | None. A restatement of the same fact. |
| 5 | Extend P to a global complement E (§3) | ELEM | Graph of χA over N_F; any graph over N_F is complementary to T | None. |
| 6 | Oblique tube Q with DQ(F)\|_E = 0 (§2) | ELEM | Inverse function theorem for Φ(p,e) = F(p)+e, plus compactness for uniform injectivity; orthogonality unused | None. Also optional; see route E2 in `review.md`. |
| 7 | Oscillation w ∈ P, mean zero, smooth zero outside D | PAID-S | `lem:velocity-loop`, `eq:velocity-mean` | None. |
| 8 | Exact maps with df̃_z = dF + w dx + o(1) globally; exterior C² error kept | PAID-S | `prop:primitive-realization`, `eq:realization-asymptotics`, exterior C² clause; `prop:exact-correction` o(1) in C² (applied in that proof) | None. Combining disk and exterior estimates is immediate. |
| 9 | Global C⁰ closeness (§4) | PAID-S (proof ops) or ELEM | `eq:finite-ansatz`, coefficient bound O_s(s^{−p₁}) after `eq:slow-map-bounds`, `eq:fast-asymptotic-scale`/`eq:slow-scale-choice`, `eq:slow-induction` (G_m → F in C³), exact-correction o(1). The author's alternative: bounded mean-zero primitive plus an exterior anchor | None. The paid route depends on reading the coefficient bound as covering U_j; the author's route needs no such reading. |
| 10 | Q∘f̃_z → F in C¹ (§5, (5.2)) | ELEM | Chain rule plus DQ(F)w = 0 plus uniform continuity of DQ on a compact sub-tube | None. |
| 11 | Single-step injectivity (§5) | ELEM | C¹ openness of compact embeddings (proved in §2); a collision for f̃_z gives one for Q∘f̃_z; positive metric gives immersion | None. Route E2 gives the same result directly, with the near/far structure of DLIS's final proof of Theorem 1.2. |
| 12 | Preserve all source invariants at the same z | PAID-S | `geometry-preservation.tex`: "Choose z small enough for these properties…" | Take the minimum of two step-dependent thresholds. |
| 13 | Finite induction to metric g | PAID-S | Proof of `thm:main` (finite list; constants chosen per fixed step) | Add injectivity to the inherited invariants. |
| 14 | Disconnected and empty M | ELEM | Finitely many components; translations | None. |
| — | Identify w ∈ P and project along P | **NEW-OBS** | Combines items 4, 7, 8 with items 5, 6, 10, 11 | **The only author-specific idea. Judged not substantial (see below).** |

## Why the NEW-OBS row is not substantial

- Its geometric content (P transverse to T) is literally a conclusion of the
  source's `lem:velocity-plane`. Its analytic content (w ∈ P with bounded
  derivatives, exact maps, o(1) errors) is the source's realization contract.
  What remains is linear algebra (a fixed linear map with kernel P) followed
  by standard near/far embedding stability.
- The primary bodies I read treat finite-step embedding retention under
  oscillatory metric corrections as standard or secondary: DLIS 2018
  (Theorem 1.2 introduction, Remark 8.1, final proof of Theorem 1.2),
  Cao–Székelyhidi 2306.12879v1 (p. 14, end of the Proposition 3.3 proof), and
  Le Donne 1005.1623v2 (Theorem 3.1, "Consequence of Nash's proof"). None of
  them states the present large oblique case verbatim. The adaptation changes
  only the near-pair lower bound, and that change needs no new estimate.
- There is no added estimate with derivative loss, no new correction, no
  parameter or sign change to a paid formula, and no compatibility argument.

## What standard alternatives fail, and why that does not create substance

| Alternative | Fails? | Reason | Effect on classification |
|---|---|---|---|
| C⁰ closeness alone | Yes | Small immersed self-crossings are C⁰-small | Shows a real bridge is needed; the bridge is item 11 |
| Orthogonal nearest-point projection | Yes | Exact two-jet: π_T X = (−1, 0) (`checks.json`) | The fix uses the paid complement P |
| Verbatim DLIS (8.2) pointwise mean-value bound | Not available as a black box | Chord averages lie in F_x + conv{w}; an exact convex combination has zero orthogonal tangential part and squared length 1/4 < \|F_x\|² = 1, although every single phase has \|X\|² = 2 (`checks.json`) | A fixed linear map killing P handles all such averages at once |
| R⁵, C¹, local, or immersion-only theorems | Not the target | Scope | Not used |
| Whitney/general-position double-point removal | Not used | It would not preserve the isometric metric | Not needed |

## Comparison with earlier family333 chains (actual bodies)

| Chain | Operation | Relation |
|---|---|---|
| `fresh-parent-discovery-r5/screen.md` | Finite exterior Cᵐ control by rescheduling exact-correction indices; noncompact-exhaustion gap; obstruction to extending an arbitrary local map | Different target. The present proof uses neither the refinement nor any extension. |
| `fresh-analytic-discovery-r17/source-reading.md` | Navigation and contract reading; notes that the loop gives no global C¹ closeness or injectivity preservation | The present note bridges exactly that point by projection. This is not a duplicate. |
| `fresh-structural-discovery-r92/screening.md` | K > 0 ⇒ H ≠ 0 ⇒ zero normal Euler class; rejects prescribed regular-homotopy classes | No class is prescribed here. Embedded closed orientable surfaces in R⁴ have normal Euler number 0, so there is no conflict. |

Distinctness from these chains is necessary but not sufficient. It does not
change the TECHNICAL classification.

## Source334

Theorem A of `A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space`
(`build/main.tex`, read in full) is a local R³ smooth nonimmersion result. It
pays and obstructs nothing in the R⁴ injectivity argument.
