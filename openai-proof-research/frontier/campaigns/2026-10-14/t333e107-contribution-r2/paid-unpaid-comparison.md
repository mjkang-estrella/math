# T333E107 r2: paid / unpaid operation comparison

Contribution comparison conditional on correctness. Verdict: TECHNICAL. There
is no proof-gate decision, count or acceptance. Source paths are under
`preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/build/`
at the pin `fd4aeeb2…`. Line numbers refer to the retained TeX, which is
authenticated against the complete 13,223-entry tree. "Author §n" refers to
`fresh-analytic-discovery-r107/proof.md`.

| # | Author step | Paid by (exact label / location) | What is added | Class |
|---|---|---|---|---|
| 1 | Start from an embedding into S^3 | Classical: closed orientable surface = boundary of a handlebody in R^3; inverse stereographic projection | Choice of starting map | Standard topology; not an isometric theorem |
| 2 | Keep the embedding through preparation | `global-construction.tex` `lem:spherical-preparation` l.34 ("every 0<ε<ε_0", ε-independent C, c); proof of `lem:global-preparation` l.122 (fixed I, uniform family, one λ) | Restrict ε below the C^1-openness radius of I | Paid quantifier plus an elementary fact (author §2) |
| 3 | Metric decomposition, convex phases, γ^K = g, phase Hessian | Same lemma; `eq:global-amplitudes` l.239; `eq:cycle-identity` l.248 | Nothing | Paid |
| 4 | P ⊕ T = R^4 on a collar of D̄ | `velocity-loop.tex` `lem:velocity-plane` l.35–52: Γ^x_yy<0 ⇒ "tangential projections of Y,C independent"; "projection to P restricts to an isomorphism on the normal plane" | Dual statement (P∩T)^⊥ = span(Y,C)+N | Paid (dual linear algebra); exact check part B |
| 5 | Oscillation w ∈ P, mean zero, flat at C_0, any amplitude | `lem:velocity-loop` l.347; `eq:leading-velocity` l.83; `eq:velocity-mean` l.184 | Nothing | Paid |
| 6 | Linear cancellation DQ(F)w = 0 | `eq:leading-metric` l.88: X = (G_x − v) + V, with G_x − v ∈ span(Y,C) and V, v ∈ P. So proj_{span(Y,C)} X = proj_{span(Y,C)} F_x | DQ(F(p)) = (Π|_T)^{−1}∘Π, with Π the orthogonal projection onto span(Y,C) | Paid splitting plus a 2×2 inverse (review R3) |
| 7 | Global complement E | none | Cutoff graph over N_F | Elementary bundle algebra |
| 8 | Tube retraction Q along E | none in source; classical tubular neighbourhood for an arbitrary complement | Inverse function theorem plus compactness (author §2) | Classical |
| 9 | Global C^0 closeness f̃_z → F | `primitive-realization.tex` `eq:finite-ansatz` l.89; `eq:slow-map-bounds` l.264 (G→F in C^3); coefficients O_s(s^{−p_1}); `eq:fast-asymptotic-scale` l.302 (σ(p_1+2)<1); `prop:exact-correction` (C^2 o(1)) | Author re-derives it from the stated asymptotics (mean-zero W plus exterior anchor) | Paid in the proof operations; the re-derivation is elementary |
| 10 | df̃_z = dF + w dx + r_z globally, r_z→0, df̃_z bounded | `prop:primitive-realization` l.11, `eq:realization-asymptotics` l.47 (exact maps, uniform on D̄); exterior C^2 convergence | Extend w dx by zero | Paid |
| 11 | Q∘f̃_z → F in C^1 | none | Chain rule plus uniform continuity of DQ | Elementary |
| 12 | Single-step injectivity | none | C^1 openness for Q∘f̃_z; f̃_z(p)=f̃_z(q) ⇒ Q-equality ⇒ p=q | Elementary; the DLIS Remark 8.1 near/far skeleton gives an equivalent route |
| 13 | Simultaneous source invariants | `geometry-preservation.tex` l.279 (z small for all properties; F_+ = f̃_z) | Minimum of two thresholds | Paid plus a finite minimum |
| 14 | Finite assembly, components, empty case | Final proof of `thm:main`; component reduction at the start of `global-construction.tex` | Translations separate the compact component images | Paid plus a trivial step |

**Unpaid by the source:** the injectivity conclusion and steps 7, 8, 11 and
12. **Unpaid and substantial:** none. Each unpaid step is an elementary or
classical operation applied to paid data. The single source-specific idea is
to use the source's own complement P as the tube fibre. That is a choice
inside paid linear algebra (rows 4 and 6), not a new mechanism.

## Standard alternatives and why the author did not need them

- *Orthogonal tangent projection* (the classical Kuiper-style argument)
  fails. For A > π loops the orthogonal x-component 1/5 + (6/5)cos t changes
  sign (exact, part A), and in a float model the projected map folds
  (part C). This failure does not make the fix substantial: see row 6.
- *C^0 closeness alone* is insufficient: tiny local self-crossings are
  possible. The author does not use it alone.
- *A general-position double-point count* would be insufficient in R^4 and
  is not used. *Nash C^1 / C^{1,α} embedding theorems* lack smoothness and
  are not used. *R^5* is not the target.
- *Black-box primary theorems* (DLIS Thm 1.2, Cao–Székelyhidi Prop 3.3) carry
  C^1-small or δ-small hypotheses. They are not invoked for the large oblique
  loops; the reduction above is self-contained.

## Primary comparisons, qualified

- De Lellis–Inauen–Székelyhidi, Rev. Mat. Iberoam. 34 (2018). Theorem 1.2,
  Remark 8.1 (pp.1140–1141), final embedding proof (pp.1143–1144). Finite-step
  embedding preservation with a near/far-pair split is an explicit,
  self-described "well-known" subsidiary operation. Its literal hypotheses
  are not those of the r107 step.
- Cao–Székelyhidi, arXiv:2306.12879v1. Proposition 3.3 and complete §3.1 proof:
  normal corrugation, tangential term O(δ), and "the argument for that v is an
  embedding is standard" (p.14). C^{1,θ}, small amplitude.
- Le Donne, arXiv:1005.1623v2, §3. Theorem 3.1 states, as a "Consequence of
  Nash's proof", that smooth 1-Lipschitz embeddings can be approximated by
  smooth embeddings whose length distortion is close to 1. This is
  corroborating context that smooth order-one Nash steps keep embeddings.
  Nash's body was not read and receives no operation credit.
- Gromov 2015 (pp.47–48, 58 of the manuscript text): context only (Question 55,
  elliptic immersions, closed-surface R^5 immersions).

No literature-wide absence or priority claim is made in either direction.
