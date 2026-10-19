# Operation comparison for the complete frozen T333E107 target

This is an independent contribution comparison conditional on correctness.
Verdict: TECHNICAL. Distinct from earlier family333 screens; not substantial
under the campaign criterion. No proof-gate verdict, count, or acceptance.

## Paid source interfaces: exact labels and locations

All source paths below have prefix
`preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/build/`
at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The private provenance records
their pinned raw URLs and complete-tree Git blobs. Line numbers refer to the
retained TeX; semantic reading covered the whole files, not just these labels.

| Author operation | Already paid / elementary reduction | Residual at full target |
|---|---|---|
| Start with embedding in S3 | Ordinary orientable-surface handlebody embedding in R3, then inverse stereographic projection | Standard topology; no isometric theorem imported |
| Retain injectivity during preparation | `global-construction.tex`, `lem:spherical-preparation`, full proof; `lem:global-preparation`, full proof begins with any fixed I and uniform family | Restrict the available C1 tolerance using compact embedding openness |
| Obtain the precise final metric and convex phases | Same `lem:global-preparation`; `eq:global-amplitudes`, `eq:cycle-identity` | None: author changes no phase, amplitude, cone, or cycle construction |
| Obtain smooth exact primitives | `primitive-statement.tex`, `prop:primitive-addition`; `small-modes.tex`, `prop:small-increment`; `exact-correction.tex`, `prop:exact-correction`; `primitive-realization.tex`, `prop:primitive-realization` | None: all analytic accuracy, mean correction, smoothing and smooth exactness are source operations |
| Place w in a complementary plane | `velocity-loop.tex`, `lem:velocity-plane` and its Gauss-formula proof; `lem:velocity-loop`, `eq:velocity-mean` | Complementarity is the dual form of the source's independent tangential projections, not an additional condition |
| Extend the plane beyond the disk | Smooth graph over N_F and cutoff | Ordinary bundle algebra; no global trivialization or frame obstruction |
| Obtain oblique tubular base Q | Apply inverse function theorem to Phi(p,e)=F(p)+e on the complement bundle and use compactness for uniform injectivity | Elementary tubular-neighborhood construction, independent of the metric problem |
| Obtain global C0 closeness | Source `eq:finite-ansatz`, `eq:slow-map-bounds`, `eq:fast-asymptotic-scale` and exact-correction o(1) in C2; or author's bounded periodic primitive and exterior anchor | Already implicit in paid proof operations; alternate deduction uses elementary integration |
| Get df_z=dF+w dx+o(1) globally | `prop:primitive-realization`, `eq:realization-asymptotics` for the exact maps, plus exterior C2 convergence | None; no assumption of support-fixed exact maps |
| Bound first derivatives at every phase | Same exact asymptotics, or fixed smooth positive definite induced metric | None; constant may depend on this step and loop amplitude |
| Remove order-one oscillation from projected derivative | DQ(F)w=0 and chain rule, displayed identity in review.md | A useful application of ordinary transverse tubes; no new estimate with derivative loss |
| Conclude single-step global injectivity | C1 openness of compact embeddings applied to Q composed with f_z, then equality of f_z images implies equality after Q | Classical local derivative and distant-pair separation, with the required derivative control explicitly supplied |
| Preserve source invariants simultaneously | `geometry-preservation.tex`, proof of `prop:primitive-addition`, final small-z choice | Take minimum of two step-dependent thresholds |
| Finish every g on every orientable closed M | `global-construction.tex`, final proof of `thm:main` is finite | Inductively add injectivity to existing invariants; finite translations separate components; empty case vacuous |

## The source-specific calculation, without a false normal simplification

Write T=dF(TM), N=T^perp. The source's proof shows that tangential projection
span(F_y,F_yy) -> T is an isomorphism, since Gamma^x_yy != 0. Thus
P=span(F_y,F_yy)^perp has P intersection T={0}. Equivalently, normal projection
P -> N is invertible. These projection statements are dual linear algebra,
not a fresh normal-geometry lemma. In particular P need not equal N.

With E=P near the closed disk, the derivative of the resulting tube retraction
along E is identity on T and zero on P. If
df_z=dF+w dx+r_z and f_z->F in C0, the elementary estimate is

    ||d(Q f_z)-dF||_0
      <= omega_DQ(||f_z-F||_0) ||df_z||_0
         + ||DQ(F)||_0 ||r_z||_0 -> 0.

Here omega_DQ is the modulus of continuity of DQ on a fixed smaller compact
tube. No small-amplitude assumption on w occurs, only boundedness for the
fixed loop. This is the actual author's argument, not ordinary orthogonal
normal projection. It consumes exactly the source interfaces in the table.

This reduction also explains why no common reach is needed: Q and its tube
are rebuilt after the old embedding has been fixed at each of finitely many
steps. The source's internal infinite exact-correction iteration is already
paid and produces a smooth map with the stated asymptotics; this review adds
no new limiting argument to it.

## Primary antecedents: operation credit versus literal coverage

1. De Lellis–Inauen–Szekelyhidi (2018), Theorem 1.2, Remark 8.1,
   and its concluding proof: finite-step embedding retention and
   near-/far-pair estimates are explicit proof operations. Actual text read:
   retained lines 1–135, 1090–1185, 1320–1385. This is not a black-box
   all-amplitude oblique-projection theorem. In particular the vector-valued
   mean-value representation in the remark is not used in the reduction.
2. Cao–Szekelyhidi 2306.12879v1, Proposition 3.3, complete Section 3.1 proof,
   equations (3.16), (3.20), (3.21), (3.25), and concluding p.14 paragraph:
   normal corrugation, smaller tangential terms and standard embedding
   retention. Theorem 1.1 is C^(1,theta), not smooth. Neither its small delta
   hypothesis nor its normal-frame oscillation is silently transplanted.
3. Le Donne 1005.1623v2, entire Section 3: Theorem 3.1 gives smooth
   almost-length-preserving embeddings; Lemma 3.5 controls tubular path
   distance; the final proof preserves embedding in a path-isometric limit.
   This is not the cancellation estimate and is not needed as a premise.
4. Gromov's October 9, 2015 manuscript: inspected elliptic-surface and Nash
   twist passages, plus the closed-immersion R5 context, provide context
   only. No theorem there is assigned the frozen R4 embedding conclusion.

The exact oblique lemma is proved directly in review.md from elementary
operations. I do not claim the inspected papers contain its verbatim wording
or a priority-determining theorem covering this deduction. A TECHNICAL
classification does not require such a claim when the campaign rule excludes
classical machinery attached to an already paid source construction.

## Strongest attempted defenses of substantiality

**It gives smoothness and all closed orientable topologies in exactly R4.**
Yes. Smoothness, exactness, arbitrary metric size, and finite global assembly
are precisely the heavy operations already supplied by source333. The new
argument does not extend their analytic domain or solve a missing PDE.

**An immersion could self-intersect; C0 alone does not preserve embedding.**
Correct. The reduction uses C1 convergence of Q f_z, not of f_z, and proves
the needed implication for collisions. This is a genuine logical bridge,
but the bridge is the ordinary transverse tube construction and chain rule.

**Ordinary orthogonal projection fails at an allowed phase.** Correct. The
exact two-jet check is preserved. Transversality already paid by the source
means the correct nonorthogonal complement can be used as a tube fiber.
There is no extra global solvability condition on that change of fibers.
The cutoff graph supplies a global complement even without a normal frame.

**The target is different from r5/r17/r92.** Correct. r5 adjusts finite
accuracy and leaves an exhaustion gap; r17 is a navigation screen; r92 has a
prescribed normal-Euler-class obstruction. Actual bodies were read. None is
a duplicate proof of the present target. This does not overcome the present
routine-source-companion reduction.

**No inspected classical theorem itself gives smooth closed R4 embeddings.**
Correct. This establishes neither an unpaid operation nor worldwide novelty.
It would be an error to count the entire headline gain as author novelty
after stipulating the powerful analytic source operations.

## Source334 and no-count boundary

Source334's Theorem A, in its complete retained `main.tex`, concerns a metric
on (-1,1)^2 with no smooth local R3 immersion. It is cited by source333 as a
dimension comparison. It cannot distinguish an R4 immersion from an R4
embedding and supplies none of the missing injectivity work. Its uninspected
lower-level proofs do not acquire operation credit.

No substantive unpaid step remains after the explicit reduction. The
conditional contribution classification is TECHNICAL. No separate correctness
gate is decided, no R-number is assigned, and campaign 18/20 is not advanced.
