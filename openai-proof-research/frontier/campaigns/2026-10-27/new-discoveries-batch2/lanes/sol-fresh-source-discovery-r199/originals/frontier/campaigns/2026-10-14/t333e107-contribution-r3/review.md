# T333E107: independent contribution review, round r3

**Verdict: TECHNICAL, conditional on correctness.**

The full frozen theorem has a stronger conclusion than source333 (embedding
instead of immersion). Every operation the author adds, however, reduces to
operations the source already pays for, plus elementary embedding stability.
The one source-specific observation is that the source's order-one oscillation
already takes values in a plane that the source itself proves transverse to the
old tangent plane. I found no unpaid operation that meets the campaign's
substantiality standard.

This is a contribution judgement only. It is not a proof-gate PASS or FAIL, an
acceptance, an R-number, or a count. The supplied campaign state is 18/20
(R023–R040), with two remaining. This review awards zero credit and edits no
ledger. The parent integrates and decides.

## Round context

- r1 (GPT-6.1-Sol/high) ended in a provider failure ("Selected model is at
  capacity. Please try a different model.") and left six unsealed public drafts
  in `t333e107-contribution-r1/`. Those drafts argue TECHNICAL. I read the four
  prose drafts in full as prior findings only. I did not read or run their
  `verify.py` or `author-baseline.json`. Their references to `checks.json` and
  `integrity-controls.json` describe files that do not exist there, and I do not
  treat those references as completed checks.
- r2 (Claude Opus 5.5) failed with "Claude API rate limit reached. Try again
  later." It produced no output.
- r3 (this review) runs on the user-authorized Factory Opus 5.5 fallback. I
  reassessed the classification from the source text and author files. I did not
  adopt r1's conclusion. Where I agree with r1, I give my own reduction below.
  Where my reasoning differs, I say so.

Provider failures are not mathematical verdicts.

## Exact object under review

The frozen target (`scope-freeze.md`, matching its detached anchor) is: for every closed smooth orientable surface M (possibly
disconnected or empty) and every smooth positive definite metric g, there is a
smooth embedding F: M → R⁴ with F*δ₄ = g. It has no curvature, genus, size,
or analyticity hypothesis. It claims no R⁵ result, no lower regularity, no
immersion-only or local conclusion, no approximation of a prescribed map, no
regular-homotopy or knot class, and no uniform estimate. Orientability was part
of the original freeze; it was not added later. This review judges exactly that
target.

Pinned source statements and proof operations at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. I did not audit
them.

## Integrity of what was read

- The four detached author digests match: manifest
  `e3b992016df3fadbe6fc223e9f1dfb9565f435b9afe9ed81705a495453ffdb6f`, proof
  `4455d5af34e0a63e4e0af20cb9cc28bb7046667b6ad259d2fd8c59a206c115bc`, scope
  `e195f3c7f3e398865ed11ebf778f101574239af3dc6ca3d3fcc09b1c6a55c916`, operation
  comparison `8317827e7e832e4e1a0e1fa759e6c81848299f0f2f0d0b8ac25b1b2d4ee7c04f`.
  I read the author's `verify.py` before running it. It is
  read-only. My replay with the detached manifest digest passed: 34 payloads,
  26 external anchors, 13 pinned blobs, 4 primary PDFs. The author directory
  contains exactly 36 files, and my manifest anchors all 36 by SHA256.
- Separately, I recomputed the Git blob SHA-1 of every retained source file and
  compared it with the complete `sources/preprints-tree.json` (13,223 entries,
  `truncated=false`). All 12 source333 build files match their pinned paths. The
  retained `companion334-main.tex` matches the blob at
  `preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/build/main.tex`.
  The canonical source333 directory holds one manuscript: 12 build files plus
  `README.md` and `paper.pdf`.

These checks authenticate bytes. They do not establish correctness or
contribution.

## What the source already pays (labels checked in the actual TeX)

All paths are under
`preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/build/`.

1. `global-construction.tex`, `lem:spherical-preparation`. For any fixed smooth
   immersion I: M → S³ there are C, c, ε₀ such that for **every** finite P and
   **every** 0 < ε < ε₀ there is I_P with ‖I_P − I‖_{C¹} < ε, a uniform C² bound,
   and a uniform metric lower bound. The proof of `lem:global-preparation`
   begins "Fix a spherical immersion I and the uniform family of modifications"
   and chooses λ uniformly over that family. Shrinking ε only shrinks the family.
2. `velocity-loop.tex`, `lem:velocity-plane` and its proof. From
   Γ^x_yy = −Hess x(∂_y, ∂_y) < 0 (convention fixed in `preliminaries.tex`) and
   C = Γ^x_yy G_x + Γ^y_yy G_y + B_G(∂_y, ∂_y), the source proves: "The
   tangential projections of Y, C are therefore independent … Projection from the
   normal plane to P is consequently an isomorphism." This holds on a
   neighborhood of the closed disk and of the 2-jet section.
3. `lem:velocity-loop` and `eq:velocity-mean`. The vector w = V − v takes values
   in P, has mean zero in θ, depends smoothly on position and the 2-jet, and
   extends smoothly by zero outside D.
4. `primitive-realization.tex`, `prop:primitive-realization`,
   `eq:realization-asymptotics`. For all sufficiently small z there are exact
   smooth immersions f̃_z with metric γ(F) + a²dx². Uniformly on the closed disk,
   (f̃_z)_x = X + o(1) and (f̃_z)_y = Y + o(1), with X = F_x − v + V = F_x + w
   evaluated at G = F and θ = x/z. On the exterior, f̃_z → F in C². The proof
   states that `prop:exact-correction`'s ‖f̃_z − f_z‖_{C²} = o(1) "preserves all
   the derivative asymptotics."
5. `geometry-preservation.tex`. The proof of `prop:primitive-addition` takes
   F₊ = f̃_z and ends: "Choose z small enough for these properties, all the
   finite crossing conditions, and the prescribed exterior error ε." Any smaller
   z is therefore admissible.
6. `global-construction.tex`, proof of `thm:main`. The assembly has finitely many
   steps, with constants and oscillation parameters "chosen for the current fixed
   smooth data."

Because proof operations are stipulated, the author may legitimately select the
specific family f̃_z from item 4, and not merely any map satisfying the
proposition's headline. The author states this choice explicitly (proof.md,
Input 2).

## My reduction of every added step

I fix one primitive step. The current map F is a smooth embedding, the disk D
and loop w are fixed, and all constants below may depend on this step.

**A. Starting embedding (classical topology, flagged as input).** A closed
orientable surface embeds smoothly in R³ (handlebody realization). Inverse
stereographic projection then gives an embedding into S³. This is a standard
topological input. I did not read a primary body for it, and I give it no
operation credit beyond "standard." It is not where a substantiality claim could
sit. The author identifies it the same way.

**B. Preparation keeps injectivity (paid plus C¹ openness).** By item 1, choose
ε below the C¹-embedding neighborhood of I. Every allowed I_P is then an
embedding, and so is λI_P. No preparation estimate changes.

**C. Complement (paid; an exact restatement).** Let T = dF(TM), N = T^⊥, and
P = span(Y, C)^⊥. Then P ∩ T = 0 ⇔ P^⊥ ∩ T^⊥ = 0 ⇔ span(Y, C) ∩ N = 0 ⇔ the
normal-to-P projection is injective. That last condition is the conclusion of
`lem:velocity-plane` quoted in item 2. So the author's (3.2) is not a new
geometric fact. It is the source's sentence read through orthogonal complements.
`checks.json` confirms the three-way equivalence on 400 exact rational instances,
101 of them degenerate. That is a sanity check, not a proof. The proof is the
one-line duality above.

**D. Global C⁰ closeness (paid in the proof operations; the author's route is
elementary).** In the proof of `prop:primitive-realization`:
f_z[G] = G + Σ_{j≤L} z^j U_j(G; x/z) (`eq:finite-ansatz`). The expansion
coefficients and their periodic derivatives are O_s(s^{−p₁}) with s = z^σ
(text after `eq:slow-map-bounds`). Also σ(p₁ + 2) < 1
(`eq:fast-asymptotic-scale`, `eq:slow-scale-choice`), G = G_m → F in C³
(`eq:slow-induction`), and ‖f̃_z − f_z‖_{C²} = o(1). Reading "they" in the
coefficient sentence as including U_j, which is the natural reading, gives
‖f̃_z − F‖_{C⁰} ≤ ‖G − F‖ + O(z^{1−σp₁}) + o(1) → 0. That reading is
interpretive. The author's own derivation from the stated asymptotics needs no
such interpretation. Put H_z = f̃_z − F − zW(p, x/z), where W is the mean-zero
periodic primitive of w (the source's U₁ evaluated at F). Then dH_z → 0
uniformly; integrate from one exterior anchor over a connected M of finite
diameter.
Either way, this is a finite estimate from paid data. I checked the author's
version line by line and found no gap. It keeps the exterior C² error and does
not assume the exact maps are fixed outside the support.

**E. Single-step injectivity: two independent elementary routes.**

*E1 (author's oblique tube).* Let E be the graph of χA: N → T, where A comes
from P over a collar and χ is a cutoff. Then E is a global complement to T. The
map Φ(p, e) = F(p) + e has an invertible differential on the zero section. The
inverse function theorem plus a compactness argument for uniform injectivity
gives a tube, and Q = F ∘ (base projection) satisfies QF = F, DQ(F)dF = dF, and
DQ(F)|_E = 0. Write df̃_z = dF + w dx + r_z with ‖r_z‖ → 0 and w ∈ E. Then
d(Q f̃_z) − dF = [DQ(f̃_z) − DQ(F)]df̃_z + DQ(F)r_z → 0. C¹ openness of compact
embeddings then makes Q f̃_z an embedding, so f̃_z is injective. I checked each
line. This is the textbook proof of a tubular neighborhood, run with a
non-orthogonal fiber. Orthogonality of the fiber is never used; N serves only
as the reference bundle for the graph.

*E2 (my tube-free chord route).* This route shows that even the tube is
optional. Cover M by finitely many coordinate balls of radius ρ, convex in their
charts, each either contained in the collar where P is defined (using the (x, y)
chart) or disjoint from the closed disk. Take ρ below a Lebesgue number. For a
ball centered at p₀ inside the collar, let L = L_{p₀}: R⁴ → R² be the linear map
with kernel P_{p₀} and L ∘ dF_{p₀} = Id. Write Π_p for orthogonal projection
onto P_p. Integrating df̃_z along the segment from q to p (with Δ = p − q):

  |L(f̃_z(p) − f̃_z(q)) − Δ| ≤ ‖L‖ (ω_{dF}(ρ) + sup_B ‖Π_p − Π_{p₀}‖ · sup|w| + ‖r_z‖_{C⁰}) |Δ|.

Here L w(p, ·) = L(Π_p − Π_{p₀})w because L kills P_{p₀}. The quantities ‖L‖,
ω_{dF}, the Lipschitz constant of p ↦ Π_p, and sup|w| are fixed for this step
and uniform over centers in the compact collar. Choose ρ so that the first two
terms are at most 1/4. This choice is independent of z. Then choose z so that
‖L‖‖r_z‖ ≤ 1/4. Near pairs then satisfy |f̃_z(p) − f̃_z(q)| ≥ |Δ|/(2‖L‖). For
balls disjoint from the disk, w = 0 and any fixed tangential left inverse works.
Far pairs are separated by C⁰ closeness and injectivity of F. This is exactly
the near/far structure of De Lellis–Inauen–Székelyhidi's final proof of their
Theorem 1.2. The only change is that their pointwise derivative bound is
replaced by an L-projected derivative bound, and the paid transversality is what
makes that bound available.

The chord route also shows precisely why ordinary orthogonal arguments fail and
why transversality repairs them. Chord averages of the derivative lie in
F_x + conv{w} ⊂ F_x + P. In the author's hostile two-jet,
(7/12)X(θ₁) + (5/12)X(θ₂) = (0, 0, −1/2, 0) has zero orthogonal tangential
component. Its squared length is 1/4, although |X(θ₁)|² = |X(θ₂)|² = 2 ≥
|F_x|² = 1. L still returns (1, 0), as it must, because L is constant on
F_x + P. See `checks.json`. So the pointwise metric-dominance bound
|(Dū + ∂_ξw)e| ≥ |Dū e| of DLIS (8.2) holds at every single phase but fails for
convex combinations of admissible loop values. Their single-point mean-value
representation therefore cannot be transplanted verbatim to these large
vector-valued loops. A fixed linear map that kills the paid plane is enough.

**F. Assembly (paid plus a finite minimum).** Take z below both the source's
geometry-preservation threshold and the injectivity threshold. f̃_z is immersive
because its induced metric is positive definite. A compact injective immersion
is an embedding. Repeat for each of the K < ∞ steps. Translate the finitely many
components apart; translations preserve metrics. The empty case is immediate.
No common reach, limiting map, continuous dependence on z, or uniform
higher-order bound is used.

## What remains, and the substantiality judgement

After A–F, the only remaining source-specific content is one observation: *the
source's oscillation w lies in the source's plane P, which the source already
proves is transverse to T; so project along P.* Everything else is the source
itself or elementary stability (C¹ openness, the inverse function theorem,
compactness, the chain rule, finite minima).

I judge this observation not substantial under the campaign rule. My reasons:

1. The transversality is not produced by the author. It is the conclusion of
   `lem:velocity-plane`, where the source uses it as the reason the loop
   construction works (`eq:projected-yy-form`, the corrector Gram inverse, and
   the nonvanishing of S₀).
2. Embedding preservation under finitely many corrugation steps is treated as
   secondary in the primary literature I actually read. DLIS introduce Theorem
   1.2, whose last sentence is the embedding clause, as following "with little
   additional technicalities, which we believe to be of secondary importance."
   Their Remark 8.1 calls finite-step embedding retention "well-known and has
   been proved by Nash and Kuiper." Their final proof of Theorem 1.2 repeats
   that "this argument is well-known." Cao–Székelyhidi's Proposition 3.3 proof
   (p. 14) says "The argument for that v is an embedding is standard."
   Le Donne's Theorem 3.1, labelled "Consequence of Nash's proof", gives smooth
   almost length-preserving embeddings and calls this "one of the strategic
   steps of Nash-Kuiper's proof" (citing Nash 1954, eq. 26, which I did not
   read). None of these
   statements literally covers the source's large, oblique, exactly corrected
   loops. They do show that the operation class (finite-step, near/far
   injectivity retention under oscillatory corrections) is standard, and the
   adaptation E2 changes only the near-pair linear algebra.
3. The adaptation needs no new estimate, no new PDE or correction, no change of
   amplitude, phase, sign, or parameter, and no global compatibility argument.
   Thresholds are chosen after each fixed map, finitely many times.
4. The headline is striking. Smooth isometric embeddings of every closed
   orientable surface in exactly R⁴ is a natural question. The brief rules that
   a striking headline without an unpaid operation does not qualify. The
   headline's analytic weight (smooth exactness, arbitrary metric size, finite
   global assembly, preserved normal geometry) is entirely paid by source333.

**Strongest defense of SUBSTANTIAL, and why it fails.** (a) "Orthogonal
projection genuinely fails, so a new idea was needed." That is true; I confirmed
it exactly. But the replacement idea is to use the transverse complement the
source already names. That is a choice of fiber, not a new mechanism. (b) "The
classical arguments assume small or normal oscillations." Also true, and I do
not apply them verbatim. E2 shows the large-amplitude case costs only sup|w| in
the choice of ρ, which is fixed before z → 0. (c) "No inspected theorem states
the R⁴ smooth embedding conclusion." True, but that is the absence of a stated
theorem, not the presence of an unpaid operation. It confers no priority or
novelty, and I make no literature-wide absence claim.

## Each original objection, reassessed

1. *Source-companion/technical risk.* Upheld. A–F give the reduction.
2. *Classical embedding preservation (DLIS Remark 8.1 and final proof; CS
   Proposition 3.3; Le Donne §3).* I read the passages myself (extents in
   `reading-limits.md`). They do not literally cover large oblique exact loops.
   I do not rest the verdict on reading them as black boxes. I rest it on E1/E2
   being elementary and on these primaries showing that the operation class is
   regarded as standard.
3. *Orthogonal vs oblique projection.* The difference is real. The two-jet
   check is exact (`checks.json`: π_T X = (−1, 0), L X = (1, 0)). I also show a
   chord average with zero orthogonal tangential part. I do not dismiss the
   difference by appealing to C⁰ closeness. I classify the oblique choice as
   standard tubular geometry once the source's own transversality is exposed. E2
   shows the same conclusion without any tube.
4. *Orientable scope and family history.* Orientability was in the original
   freeze and is forced by the S³ starting embedding. Nonorientable closed
   surfaces do not embed in S³. I read the actual bodies. r5 `screen.md` makes a
   finite exterior Cᵐ refinement by rescheduling the paid exact-correction
   indices and leaves a noncompact-exhaustion compatibility gap. r17
   `source-reading.md` is a navigation and contract screen; its family333
   paragraph notes that "The loop construction does not provide global C1
   closeness or injectivity preservation". The author supplies exactly that
   bridge, by projection. r92 `screening.md` rejects a prescribed
   regular-homotopy extension via K > 0 ⇒ H ≠ 0 ⇒ zero normal Euler class. This
   target prescribes no class, and closed orientable embedded surfaces in R⁴
   have zero normal Euler number anyway, so there is no conflict. The present
   deduction duplicates none of them. That distinctness is necessary but does
   not establish substantiality.
5. *No support-fixing, common reach, or continuous z-selection.* Confirmed. The
   author keeps the exterior C² error (D) and chooses z per step after the map is
   fixed (F). I did not replace the mechanism with a simpler false one. E2 is an
   additional route, not a substitute premise.

## The r1 draft observations, reassessed

- *Complementarity is the dual of `lem:velocity-plane`.* Agree. The source's
  sentence about normal-plane projection is literally equivalent (C).
- *Global C⁰ is already in the paid ansatz.* Agree, with a qualification: this
  depends on reading the source's coefficient bound as covering U_j. The
  author's alternative derivation makes this immaterial (D).
- *Reduction to handlebody embedding, C¹ openness, cutoff graph, inverse
  function theorem with compactness, chain rule, finite minima.* Agree. I add
  E2, which shows the tube is optional, and the convex-combination observation,
  which explains exactly what transversality buys.
- *Orthogonal projection truly fails; C⁰ alone is insufficient; distinct from
  r5/r17/r92.* Agree, independently checked.
- *Primaries do not literally cover large oblique loops; no credit through
  unread Nash/Kuiper/Whitney/Gromov.* Agree. I also give no operation credit to
  the unread handlebody/classification primary, Lang/Hirsch-type tubular
  neighborhood texts, or Federer (cited by Le Donne).
- *No material gap; source334 irrelevant; attribution fixes do not create
  substance.* Agree; see the next two sections.

I found no point where I disagree with r1's classification. My agreement rests
on my own reading and reduction, not on the draft.

## Mathematical gaps and presentation notes (not a proof gate)

I found no mathematical gap that matters for the contribution reduction. These
are presentation notes only, and none would change the verdict:

- proof.md writes the global derivative as w(p, x/z)dx extended by zero, which
  is legitimate because w vanishes to all orders on ∂D (`lem:velocity-loop`).
  Combining "uniform on the closed disk" with "C² on the exterior" gives a
  global r_z. That is correct as written.
- The author cites no primary for the handlebody embedding of orientable closed
  surfaces. It is standard, and a manuscript should cite it.
- Attributing the complement to `lem:velocity-plane`, and citing DLIS, CS, and
  Le Donne for standard embedding retention, would make the note more accurate.
  Neither change creates an unpaid operation.

I did not run a separate correctness gate. The statement above is not a PASS.

## Source334

The retained `companion334-main.tex` (all 228 lines read) states Theorem A: a
smooth metric on (−1, 1)² with no smooth isometric immersion of any
neighborhood of the origin into R³. Source333 cites it as a dimension contrast.
It concerns local existence in R³. Its remark that a local immersion restricts
to a local embedding has nothing to do with global injectivity in R⁴. It
neither pays nor obstructs any step here. Its section files were not acquired or
read, and they are not premises.

## Literature boundary

This is a focused operation review, not a priority search. No absence of a
search hit, unread bibliography item, or abstract was used to clear or deny
novelty. I make no claim that the R⁴ embedding conclusion is new to the
literature.

## Disposition for the parent

**TECHNICAL conditional on correctness. No substantial-contribution PASS. No
count, R-number, or acceptance entered. Proof gate not decided here.** The
author packet, r1 drafts, parent files, and shared ledgers were not modified.
