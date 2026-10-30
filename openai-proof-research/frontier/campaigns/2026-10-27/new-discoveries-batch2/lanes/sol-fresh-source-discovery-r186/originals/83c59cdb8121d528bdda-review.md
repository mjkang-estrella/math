# T333E107: independent contribution review, round r2

**Verdict: TECHNICAL, conditional on correctness.** No substantial-contribution
PASS. This is a contribution judgement only. It is not a proof-gate PASS or
FAIL, it assigns no R-number, it awards zero count credit, and it enters no
acceptance. The supplied campaign state is 18/20 (R023–R040) with two
remaining; this review leaves it unchanged. The parent integrates and decides.

Round r1 (GPT-6.1-Sol/high) failed at the provider and left six unsealed draft
files. They were read in full as prior findings, not as authority (see
§8). This round was run by Claude Opus 5.5 under the user's authorized
fallback. I reached the same classification as the r1 draft, but by my own
reduction, given in §4. That reduction differs from r1's in one respect. It
shows that the author's "oblique" projection is, at the linearized level,
the **orthogonal** projection onto span(F_y,F_yy). That projection already
appears in the source's own leading-metric computation.

## 1. The exact frozen object

From `fresh-analytic-discovery-r107/scope-freeze.md` (SHA256
`e195f3c7…6c55c916`, matching the detached anchor): for **every** closed
smooth **orientable** surface M (possibly disconnected; the empty case
included) and **every** smooth positive definite metric g on M, there is a
smooth **embedding** F: M → R^4 with F*δ_4 = g. There are no curvature,
genus, analyticity, smallness or conformal hypotheses and no uniform
estimate. The theorem is not for R^5, C^1, a local result or a mere
immersion. It asserts no approximation of a prescribed map and no
prescribed knot or regular-homotopy class. Orientability is part of the
original freeze. The freeze explicitly names the unpaid operation it seeks:
"global injectivity through those large derivative changes". I judge exactly
this target. I do not substitute a weaker or stronger one.

## 2. Premise boundary and integrity

All pinned source333/334 statements **and proof operations** at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. I do not
audit them. Detached anchors matched:

- manifest `e3b992016df3fadbe6fc223e9f1dfb9565f435b9afe9ed81705a495453ffdb6f`;
- proof.md `4455d5af…5c115bc`;
- scope-freeze.md `e195f3c7…6c55c916`;
- operation-comparison.md `8317827e…d4ee7c04f`.

I read the author's `verify.py` in full before running it. Replayed with the
detached digest, it returned `integrity: verified`, with 34 payloads, 26
external anchors, 13 pinned blobs and 4 primary PDFs. The 13 retained TeX
files are checked against Git blob identities in the complete
`sources/preprints-tree.json`: 13,223 entries (10,373 blobs, 2,850 trees),
`truncated=false`. `sources/tree.json` was not used. My own verifier checks
these blobs again. This authenticates bytes only.

## 3. What source333 actually pays (actual statements and proof operations)

All paths are under
`preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/build/`.
Line numbers refer to the retained pinned TeX.

- **S1. Starting map and preparation** (`global-construction.tex`).
  `lem:spherical-preparation` (l.34) applies to *any* smooth immersion
  I: M → S^3. It gives constants C, c, ε_0 such that, for every finite P and
  **every** 0 < ε < ε_0, there is I_P with ‖I_P − I‖_{C^1} < ε, a uniform C^2
  bound and a uniform metric lower bound. The proof of `lem:global-preparation`
  (l.122) fixes I and works "uniformly for this family". λ is chosen for all
  allowed modifications, and F^0 = λI_P.
- **S2. Finite list and phase condition.** The same lemma, `eq:global-amplitudes`
  and `eq:cycle-identity`, gives γ^K = g and Hess_{γ^{j−1}} x_j(Y_j,Y_j) > 0
  on the closed disk D̄_j.
- **S3. Transverse velocity plane** (`velocity-loop.tex`). In the proof of
  `lem:velocity-plane` (l.35–52), Γ^x_yy < 0, so "the tangential projections
  of Y,C are therefore independent". The lemma also states that projection
  to P "restricts to an isomorphism on the normal plane". `eq:leading-velocity`
  and `eq:leading-metric` (l.83–88) say that G_x − v ∈ span(Y,C) and V, v ∈ P,
  whence |X|^2 = |G_x|^2 + a^2. `lem:velocity-loop` (l.347) and `eq:velocity-mean`
  give a smooth, mean-zero, 2π-periodic w ∈ P that extends smoothly by zero
  outside D. Any amplitude is allowed, including loops with A > π that
  cover the whole circle.
- **S4. Exact maps and their asymptotics** (`primitive-realization.tex`).
  `prop:primitive-realization` (l.11) and `eq:realization-asymptotics` (l.47)
  hold for the **exactly corrected** maps f̃_z. On D̄ they give
  (f̃_z)_x = X + o(1) and (f̃_z)_y = Y + o(1) uniformly, where X = F_x + w(p,x/z).
  On the exterior of D, f̃_z → F in C^2. The proof constructs f_z[G] = G +
  Σ z^j U_j(G;x/z) (`eq:finite-ansatz`, l.89), with G → F in C^3
  (`eq:slow-map-bounds`, l.264). The coefficients are O_s(s^{−p_1}), with
  s = z^σ and σ(p_1+2) < 1 (`eq:fast-asymptotic-scale`, l.302). Then
  `prop:exact-correction` gives ‖f̃_z − f_z‖_{C^2} = o(1).
- **S5. Finite-step thresholds** (`geometry-preservation.tex`). The proof of
  `prop:primitive-addition` takes F_+ = f̃_z for z sufficiently small: "Choose
  z small enough for these properties…" (l.279). Every source invariant holds
  for **all** sufficiently small z, so a further threshold can be intersected
  with it.
- **S6. Finite assembly** (final proof of `thm:main`). There are K < ∞ steps,
  each chosen for the already fixed current map, with components handled
  separately.
- **Not paid:** injectivity. `introduction.tex` l.19 says: "The result concerns
  immersion; self-intersections are allowed." No source statement or proof
  operation asserts or tracks embedding.

Source334 (`companion334-main.tex`, Theorem A) gives a smooth metric on
(−1,1)^2 with no local smooth isometric immersion into **R^3**. Source333 cites
it only as a lower-dimensional contrast. It neither obstructs nor supplies an
R^4 embedding, and it has no bearing on injectivity. It is irrelevant to this
classification.

## 4. My operation-level reduction of every added step

Fix one step j: a current smooth embedding F, a disk D and the fixed loop.
Constants depend on this fixed data only.

**R1. Starting embedding (classical topology plus S1).** A closed orientable
surface embeds smoothly in R^3: by the classification theorem it is the
boundary of a standard handlebody. Inverse stereographic projection puts it
in S^3. Smooth embeddings of a compact manifold form a C^1-open set; this is
proved in a few lines in author §2 using the inverse function theorem and
compactness. Since S1 quantifies over every ε < ε_0 with ε-independent
constants, restricting ε keeps every I_P an embedding without altering any
later choice. Scaling by λ preserves injectivity. *Classification: paid
operation S1, plus an elementary standard fact, plus standard surface
topology.*

**R2. Complement (the dual of S3, not a new condition).** Write T = dF(T_pM),
N = T^⊥ and P = span(Y,C)^⊥. Then (P ∩ T)^⊥ = span(Y,C) + N. So P ⊕ T = R^4
⟺ span(Y,C) ∩ N = 0 ⟺ orthogonal projection N → P is injective. The last
condition is the literal wording of `lem:velocity-plane`. It is also
equivalent to S3's "tangential projections of Y,C independent", that is,
Γ^x_yy ≠ 0. Exact rational checks over 3,946 random two-jets, 1,007 of them with
Γ^x_yy = 0 (mostly constructed deliberately), found zero disagreements
among these four formulations (`checks.json`, part B). *Classification: paid by S3; the author
dualizes it.*

**R3. Where the cancellation already lives in the source.** Let Π be
orthogonal projection onto span(Y,C) = P^⊥. Since w ∈ P, Π(F_x + w) = Π F_x.
This is exactly the splitting X = (G_x − v) + V behind `eq:leading-metric`.
Let Λ_p := (Π|_{T_p})^{−1} ∘ Π. Then Λ_p: R^4 → T_p is linear, is the
identity on T_p and has kernel P_p. That is precisely DQ(F(p)) in the
author's (2.1). Π|_T is invertible by R2. So the author's "oblique"
projection is, linearly, the orthogonal projection onto the source's own
frame span(F_y,F_yy), transported to T by a paid isomorphism. The only
projection that fails is the orthogonal one onto T, which the source never
uses for this purpose. *Classification: paid linear algebra (S3) plus
inversion of a 2×2 isomorphism.*

**R4. Global complement and tube (classical).** Over a collar of D̄, P is a
graph of a bundle map A: N → T. A cutoff gives E = graph(χA), and every graph
over N is complementary to T. Φ(p,e) = F(p) + e on E has invertible
differential on the zero section. The inverse function theorem, together
with compactness and injectivity of F, gives a uniform tube with base
retraction Q satisfying (2.1). This is the tubular-neighbourhood construction
for an arbitrary complement bundle, and it is proved in full in author §2.
*Classification: elementary classical differential topology. No metric
equation is solved and no geometric constraint is added.*

**R5. Global C^0 closeness (paid in the proof; the author re-derives it).**
From S4, f̃_z − F = (G − F) + Σ_j z^j U_j + (f̃_z − f_z). The first term tends
to 0 in C^3. The sum is O(z^{1−σp_1}) → 0, since σp_1 < 1. The last term is
o(1) in C^2. So f̃_z → F in C^0 is already a consequence of the paid proof
operations. The author's alternative route also works, using only the stated
asymptotics: H_z = f̃_z − F − zW(p,x/z), with dH_z → 0, one exterior anchor
and finite diameter. Neither route is a new convergence scheme. The exterior
C^2 error is kept, and no support-fixing is assumed.

**R6. Cancellation and single-step injectivity (chain rule plus C^1
openness).** By S4, df̃_z = dF + w dx + r_z with ‖r_z‖_0 → 0 and df̃_z
bounded. Then
d(Q∘f̃_z) − dF = [DQ(f̃_z) − DQ(F)]df̃_z + DQ(F)r_z → 0, using DQ(F)w = 0,
R5 and uniform continuity of DQ on a compact sub-tube. Hence Q∘f̃_z → F in
C^1. It is therefore an embedding (R1's openness), so f̃_z is injective. It
is immersive by the exact positive metric, hence an embedding.

An equivalent route without the nonlinear tube follows the near/far-pair
skeleton of De Lellis–Inauen–Székelyhidi, Remark 8.1.
- *Near pairs.* For p, q in a small convex chart ball, apply the frozen
  linear map Λ_p (globally, Λ_p := DQ(F(p)), with kernel E_p; E_r = P_r
  wherever w(r) ≠ 0) to f̃_z(q) − f̃_z(p) = ∫ df̃_z. The integrand becomes
  Λ_p dF + (Λ_p − Λ_r) w dx + Λ_p r_z, which equals dF_p + O(ω(ρ)) + o(1).
  This gives a lower bound |f̃_z(q) − f̃_z(p)| ≥ c|q − p|.
- *Far pairs.* These are separated by C^0 closeness.

Either way the step reduces to calculus applied to the paid contract S4 plus
the paid transversality S3. *Classification: classical machinery.*

**R7. Assembly.** Take the minimum of the R6 threshold and the S5 threshold,
for each of the K < ∞ steps, after the current map has been fixed. No common
reach, uniform estimate, continuity in z or limiting embedding is needed.
Separate the finitely many component images by translations; the empty case
is trivial. *Classification: paid S5/S6 plus a finite minimum.*

**Residual after R1–R7.** Nothing remains except choosing, as tube fibre, a
complement already supplied and proved transverse by the source. This choice
uses no new estimate, PDE, topological elimination of double points or
global compatibility argument. I therefore classify the deduction as a
technical, source-companion application of classical embedding-preservation
methodology to source333's finite construction.

## 5. Strongest case for substantiality, and why it does not prevail

1. *The headline is strong.* The source pays exactly the
   heavy parts: smooth exactness for arbitrary metrics, convex phases, finite
   assembly, and normal and boundary geometry. Upgrading immersion to
   embedding adds no new analytic domain. The campaign rule explicitly
   excludes "striking headlines without an unpaid operation".
2. *The source allows self-intersections, and C^0 closeness alone does not
   preserve embeddings.* Both statements are true. I do not dismiss the
   problem by appeal to C^0. The bridge is R6, which is an
   ordinary chain-rule estimate once the kernel is chosen inside P.
3. *Orthogonal tangent projection genuinely fails (objection 3).* I confirm
   this with the author's two-jet in exact arithmetic. The orthogonal
   x-component of X is 1/5 + (6/5)cos t, which ranges over [−1, 7/5]. At
   V = −(3/5)(2e_1+e_3) it gives −e_1, while L(X) = (1,0). In a float model,
   the orthogonal tangent projection of a mean-zero A > π oscillation folds
   along y = 0, while the oblique-projected derivative error is about 1e−12
   and the raw derivative error stays near 2 (`checks.json`, parts A and C).
   So the author's choice of complement is a real, correct design choice.
   It is not a new operation, however. By R3 it amounts to projecting
   orthogonally onto span(F_y,F_yy), the very frame in which the source
   splits X. The tube along a general complement is textbook-level, and the
   author proves it in a dozen lines.
4. *The closest primary bodies are not literally applicable.* DLIS's Theorem
   1.2 and final proof (pp.1143–1144) use C^1 smallness ‖Du − Du_0‖ ≤ ω.
   Cao–Székelyhidi's Proposition 3.3 has amplitude δ^{1/2} with δ ≤ c_0^{−1}.
   Both theorems are C^{1,α}. I agree that neither theorem pays the
   all-amplitude smooth case verbatim, and my verdict does not depend on
   invoking them as black boxes. They are cited as primary evidence that
   finite-step embedding preservation by near/far separation is an
   established subsidiary operation. DLIS Remark 8.1 calls it
   "well-known… proved by Nash and Kuiper", and Cao–Székelyhidi p.14 calls
   it "standard". The present argument is a correct instance of that
   operation. I do not rely on the single-point vector mean-value
   representation in Remark 8.1, and neither does the author. Nash and
   Kuiper were not read, and I assign them no operation credit.
5. *It is distinct from earlier family333 chains (objection 4).* This is
   true; see §7. Distinctness is necessary but not sufficient.

## 6. Mathematical-gap assessment (not a proof gate)

Under the stipulated contracts I found no gap material to this conditional
reduction. Points I specifically checked:

- Restricting ε in S1 is legitimate because the lemma's quantifier is
  "every 0 < ε < ε_0" with ε-independent constants.
- In S5, F_+ really is the f̃_z family itself, chosen for all small z.
- The asymptotics in S4 hold uniformly on the closed disk, with C^2
  convergence on its exterior, so (5.1) is global with w dx extended
  smoothly by zero (w is flat on C_0).
- P ∩ T = 0 holds on the closed disk and persists on a collar.
- The cutoff graph is a complement everywhere.
- Section 4's anchor exists because D̄ ≠ M.

Orientability is used only to start from an S^3 embedding. It was frozen
from the outset (scope-freeze text), not shrunk after an obstruction. The
argument does not cover nonorientable surfaces, and the author does not
claim that it does. This is not a separate proof-correctness PASS, which
remains for the proof gate.

## 7. Same-family chains (actual bodies read)

- **r5 `screen.md`** (sha `1aabf5a2…`). It gives a finite exterior C^m
  refinement by restarting the exact-correction schedule at k_0 ≥ max(10, 2m),
  together with a smaller σ. It leaves noncompact exhaustion compatibility
  open and gives a flat-disk/handle obstruction to extending a prescribed
  local map. Its operation is a parameter refinement, which differs from the
  present step.
- **r17 `source-reading.md`** (sha `80691b1a…`) and the r17 `candidate.md`
  remark (sha `493a4141…`). These are navigation only: "The loop construction
  does not provide global C1 closeness or injectivity preservation." This is
  consistent with the present review. Q∘f̃_z is C^1-close, but f̃_z itself is
  not.
- **r92 `screening.md`** (sha `5ccd1750…`). It rejects a prescribed
  regular-homotopy extension using the positive-curvature normal-Euler
  obstruction. The present target prescribes no class.

None of these supplies a duplicate or recycled verdict. The TECHNICAL
classification rests on §4 alone.

## 8. Reassessment of the r1 drafts and of every carried objection

The r1 drafts read were `review.md` (7200ca89…), `paid-unpaid-comparison.md`
(f35b226e…), `reading-limits.md` (c8585134…) and `README.md` (2d4551a4…), with
`author-baseline.json` and `verify.py` as files. The r1 README and limits
refer to `checks.json`, `integrity-controls.json` and a seal. None of these
exists in the r1 directory, so those claims are unauthenticated. The r1
statement that the primary URLs were "opened with the web tool" is likewise
unverifiable, and I do not adopt it.

Each concrete r1 observation, reassessed independently:

- *Complementarity is dual linear algebra.* Agree; proved exactly in R2.
- *C^0 is in the paid ansatz.* Agree; checked against `eq:finite-ansatz`,
  `eq:slow-map-bounds`, `eq:fast-asymptotic-scale` and `prop:exact-correction`
  in R5. The author's mean-zero/anchor route is an equivalent elementary
  re-derivation.
- *Every added step reduces to elementary tools with no common reach.* Agree.
  I add R3: linearized, the oblique projection is the source's own orthogonal
  span(Y,C) projection.
- *Orthogonal projection fails, C^0 alone is insufficient, and the step is
  distinct from r5/r17/r92.* Agree; verified in exact arithmetic.
- *No black-box use of classical theorems for large oblique loops.* Agree.
- *Source334 is irrelevant; attribution fixes are not operations.* Agree.

Original objections 1–5 are each resolved as above, with every quantifier
preserved. Objection 5 is honoured: the exterior C^2 error is kept, no
support-fixing is assumed, and no infinite iteration, common reach or
continuous scale selection is used.

**Attribution versus operation.** A publishable note should present R2/R3 as
the source's transversality and cite classical embedding preservation. Those
are presentation fixes. No unpaid substantial step remains to be repaired.

## 9. Disposition

**TECHNICAL, conditional on correctness. No substantial-contribution PASS. No
count, no R-number, no acceptance. Campaign remains 18/20 as supplied.**
The parent integrates and decides. The author files, r1 drafts and shared
ledgers are unchanged. `t333e107-contribution-r3/` and
`t333e107-parent/contribution-disposition.json` exist on disk. I
deliberately did not open them, to keep this round independent, and I take
no position on their contents.
