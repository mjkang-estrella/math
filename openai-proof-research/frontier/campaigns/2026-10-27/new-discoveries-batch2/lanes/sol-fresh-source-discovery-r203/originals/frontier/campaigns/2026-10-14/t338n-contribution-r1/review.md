# T338N contribution review r1 — nonnegative-bisectional uniformization

Reviewer role: contribution and eligibility, conditional on correctness. The separate
proof gate owns the full mathematical audit; this review does not read it and does not
infer its result. Verdicts here concern whether the candidate adds substantial new
mathematics beyond its paid/stipulated inputs, for the FULL UNCHANGED TARGET:

> Every connected simply connected complete noncompact smooth Kähler manifold M of
> finite complex dimension n>=1 with nonnegative holomorphic bisectional curvature is
> biholomorphic to C^k times a finite product of irreducible compact Hermitian
> symmetric spaces, k>=1, empty compact product allowed; no upper-curvature, growth,
> decay or pinching assumption; no flatness claim for the original metric on C^k.

Frozen author packet: `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r89/`,
external anchors as supplied in the parent brief. All nine external SHA256 anchors
recomputed and matched exactly on 2026-10-18 (see checks-receipt.json). The author
verifier `verify.py` was read before running and executed with the externally supplied
manifest anchor: `PASS_IDENTITY_ONLY`, 16 public files, `full_theorem_verified:false`.
The scope-status.json target string is verbatim identical to the brief's target;
scope-status predates completion.json's assembly timestamps, as stated.

## Verdict

**TECHNICAL** for the full unchanged scope, conditional on the separate proof gate.
Not SUBSTANTIAL, not DUPLICATE, not INELIGIBLE, not BLOCKED.

The candidate is a correct-shaped assembly in which every operation is one of:
(i) a stipulated source338 proof operation reused at hypotheses the author audited
down to nonnegativity; (ii) a published primary theorem used inside its actual
hypotheses (Ni–Tam Thm 4.2(i), Gu Thm 1.1/Mok, Berger, de Rham, Bonnet–Myers);
(iii) a standard textbook device (scalar strong maximum principle, compact-chart
localization of an already-local Bony-type maximum principle, stabilizer twirl); or
(iv) a black-box application of source338's main theorem at its original strict
hypotheses. No new estimate, construction, or mechanism absent from the union of the
sources is required. The conditional resolution of the full target is real and the
scope is unchanged, but per the campaign rubric a routine robust transfer and a
verified-hypotheses reuse do not count as substantial new contribution, however long
the audit trail. No exact published duplicate was found within bounded search; this
is not a worldwide priority claim.

## Operation-level reduction preserving all quantifiers

The full target reduces, operation by operation, to paid or standard inputs:

1. **Splitting + strict psh input.** Ni–Tam arXiv:math/0304096v1 Thm 4.2(i) (read at
   extracted lines 1778–1823 of the packet's private text): hypotheses are exactly
   complete noncompact Kähler, nonnegative holomorphic bisectional curvature, simply
   connected; no curvature upper bound. Conclusion: holomorphic isometric product
   N × M′, N compact simply connected, M′ complete noncompact with a smooth strictly
   psh function of bounded gradient (their Lemma 4.1(ii): sup|∇v|≤1, lines 1471–1517).
   Bounded gradient gives the linear upper bound ψ≤C(1+r) that source338's
   Proposition initial-data(i) actually consumes. Simple connectedness of M′ and
   dim_C M′≥1 are immediate. Quantifiers match the candidate's use exactly.
2. **Compact factor.** Gu arXiv:0707.0035v1 Thm 1.1 (= Mok's generalized Frankel,
   read in full, 357 extracted lines) applies to N as its own universal cover. The
   CP^{N_i} factors carry auxiliary nonnegative-bisectional metrics θ_i, but the
   target's conclusion is biholomorphic, so this is sufficient as stated.
3. **Source front half at nonnegative hypotheses.** Source338 (pinned
   fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb) preliminaries/flow/discs/variation/
   ellipsoids. I independently confirmed the two strictness use-sites the author
   identifies and found no third one in the passages I read:
   - preliminaries.tex: the Busemann second-variation estimate uses strict
     positivity only to produce the smooth strictly psh ψ with ψ≤1+r (Richberg);
     every later operation in the section uses nonnegative curvature signs only
     (Demailly–Skoda tensor-with-determinant for T^{1,0}⊗K^{-1}; Ricci≥0 for
     Bishop–Gromov, Li–Yau, Souplet–Zhang; bisectional≥0 for the Hodge-heat
     null-vector reaction and the dd r² upper comparison).
   - flow.tex lines 84–88: the initial scalar bound P_t(0)≤C/L² is one-sided and
     uses only R_g≥0 (the prose word "positivity" is inessential); the
     largest-eigenvalue exchange at lines 159–170 discards
     −Σλ_i^{−1}R_g(i,ī,1,1̄) using nonnegativity only.
   Substituting Ni–Tam's ψ for the Busemann/Richberg construction is a one-for-one
   interface replacement with matching output; it does not alter any later estimate.
4. **Completeness of positive-time slices.** Source338 charts.tex lines 38–165
   (read): matrix/scalar Harnack are derived from joint positivity before
   completeness; the integrated Harnack is proved without minimizing geodesics; the
   quadratic curvature bound, first-exit index estimate and exit-distance ODE
   1+l_L(t)≥(1+L)e^{−2C_T√t} are the source's own argument. The only strictness
   input is division by R>0, which the source gets from A>0. The candidate replaces
   A>0 by the scalar strong maximum principle applied on compact cylinders
   (R_t=Δ_hR+|Ric_h|², R≥0, nonflat ⇒ R>0 somewhere initially by smooth convergence;
   flat ⇔ R≡0 under nonnegative bisectional by polarization). This is the standard
   strong maximum principle, and discarding the source's strict-Ricci power
   contraction (charts.tex lines ~75–83) is a free weakening: completeness does not
   use it. The strict covector estimate (charts.tex ~330–360, read) is correctly
   excluded rather than silently reused.
5. **Null propagation without a global curvature bound.** Brendle–Schoen
   arXiv:0705.3963v1 Prop 1 (read, extracted lines 55–155) is already local on an
   arbitrary Euclidean open set with compactly supported coefficients; Prop 2 (read,
   lines 156–205) reduces to Prop 1 by a cover. The candidate's finite-chart cover
   of a compact parallel-transport path, with the Cao–Chen–Zhu reaction constant
   c_K finite on each compact spacetime region of the smooth flow, is the standard
   localization of an already-local statement. u≥0 and smoothness are hypotheses
   paid by step 3, not conclusions. This is explicitly and correctly not nominated
   as substantial by the author.
6. **Fixed-time factorization.** At one fixed complete positive-time metric:
   de Rham (Beauville's notes explicitly permit complete noncompact) + parallel
   complex structure gives holomorphic factors; Berger's list for nonsymmetric
   irreducible Kähler leaves U(d), SU(d), Sp(d/2); SU/Sp are Ricci-flat, and
   Ricci-flat + nonnegative bisectional ⇒ flat by polarization (elementary);
   locally symmetric irreducible ⇒ parallel Ricci ⇒ Ric=λh; λ=0 flat, λ>0 compact
   by Bonnet–Myers, and compact positive-dimensional complex factors are excluded
   because the strictly psh ψ restricts to a compact leaf (Δψ>0 integrates to 0).
   All classical; the compact-exclusion-via-strict-psh device already appears in
   Ni–Tam's own splitting argument.
7. **Strict positivity on each U(d) factor.** The zero-pair propagation, the
   reaction inequality, the first-variation eliminations and the two-plane rotation
   R(ṽ,ṽ̄,ẁ,ẁ̄)=(H(e1)+H(e2))/4>0 are verbatim the Gu (Thm 1.2 proof) /
   Cao–Chen–Zhu (Thm 2.8 proof, extracted lines 689–1047 read) mechanism, which
   those authors credit to Mok. H>0 via U(d)-transitivity on the sphere plus
   polarization plus parallel propagation of flatness is the standard Mok Prop 1.1
   content (Gu cites it as such). One genuine gap-fill relative to the DISPLAYED
   primary proofs: Gu's P is the orthonormal 2-frame bundle and CCZ's concluding
   rotation is displayed for orthonormal pairs, while source338's hypothesis needs
   R(X,X̄,Y,Ȳ)>0 for all linearly independent pairs. The candidate's stabilizer
   twirl (write Y=aX+bZ, average the zero identities over the U(d−1) orbit of Z,
   mixed terms vanish, H(X)>0 forces a=0) closes this. It is a standard
   representation-theoretic averaging device of a few lines; CCZ already define P
   on all pairs and prove the reaction inequality there. I class it as routine,
   not as a substantial new operation; see the discussion below.
8. **Final application.** Source338's main theorem (introduction.tex, read in full)
   applies to each complete noncompact strictly-positive factor at its ORIGINAL
   hypotheses — the factor metric h_{t0}|factor is complete (de Rham factor of
   complete), the factor is simply connected noncompact, and strict positivity is
   step 7's output. Biholomorphism per factor to C^{d_i}; product with the flat
   factor gives X≅C^k, k≥1 because X is noncompact; step 2 completes the target.
   n=1 needs no separate case (holonomy U(1); H>0 is the whole conclusion).

Every quantifier of the full target is preserved: all n≥1, no hypothesis at infinity,
k≥1 from noncompactness, empty compact product allowed (Ni–Tam Remark 4.1(a)), and
no flatness claim for the original metric anywhere in the chain.

## Why not SUBSTANTIAL

- The stipulated source338 supplies every hard analytic operation: the
  unbounded-curvature localized flow, the scalar comparison before completeness, the
  disc/ellipsoid joint-positivity machinery, and the Harnack→completeness argument.
  The candidate's front-half work is a hypothesis AUDIT of that proof (verifying
  nonnegativity suffices at each use site) plus two substitutions whose outputs
  match the consumed interfaces exactly. An audit, even a long one, certifies
  robustness of an existing proof; it is not a new construction or estimate.
- Ni–Tam Thm 4.2(i) exists precisely to produce a strictly psh bounded-gradient
  function under nonnegative bisectional curvature without curvature bounds; using
  it in place of Busemann/Richberg is the canonical move an expert would attempt
  first. Source338's own introduction cites Ni–Tam's heat deformation.
- The fixed-time viewpoint (split one slice instead of tracking a time-dependent
  de Rham splitting) is an elementary logical simplification that avoids — rather
  than solves — the backward-uniqueness question CCZ address under bounded
  curvature.
- The strong maximum principle for R>0, the compact-chart localization of
  Brendle–Schoen Prop 1, Berger/de Rham/Bonnet–Myers, and the stabilizer twirl are
  all standard tools used at their standard hypotheses.
- Campaign precedent is consistent: candidates whose every operation is paid by
  stipulated sources plus published primaries plus standard devices were classified
  TECHNICAL (fk-frechet r1, poly-zp r1, artin-root r1, nodal-power-four r1,
  brenier-logconcave r1), including cases conditionally resolving named open
  problems.

## Why not DUPLICATE, INELIGIBLE or BLOCKED

- Not DUPLICATE: source338 states no nonnegative-curvature corollary anywhere in
  its build tree (my grep over all 13 pinned blobs; only antecedent discussion).
  CCZ Thm 2.8's reduction is explicitly bounded-curvature (their lines 689–704
  statement; Shi existence and the global maximum-principle application both
  consume boundedness) and its conclusion is the weaker "admits a bounded positive
  metric" alternative. Liu Thm 1.1 (extracted lines 1–150 read) requires maximal
  volume growth. Chau–Tam retain bounded curvature plus growth/decay. Bounded web
  searches on 2026-10-18 (queries logged in checks-receipt.json) surfaced the
  2026 surface results of Datar–Pingali–Seshadri (positive sectional curvature,
  dimension 2) and Wu (conditional, surfaces) and no all-dimension nonnegative
  uniformization theorem independent of source338. Bounded campaign/companion
  history search found no prior nonnegative-bisectional uniformization candidate;
  accepted findings R001–R039 contain nothing in this area. Bounded search only;
  no worldwide priority claim.
- Not INELIGIBLE: scope is unchanged (target string verified verbatim against the
  brief); all external primaries are used inside their actual hypotheses; the
  candidate makes no acceptance/count/priority claims and explicitly flags its
  finite checks as bookkeeping only.
- Not BLOCKED: all required source and primary interfaces were available, anchored,
  and read at the level described below. No missing input prevents the contribution
  classification. Correctness itself is the separate proof gate's domain.

## Required objections

None. The contribution classification does not depend on any repair. (Mathematical
completeness objections, if any, belong to the proof gate.)

## Optional items

- O1. candidate.md's phrase that Cao–Chen–Zhu Thm 2.8 "already proves the reduction
  from bounded nonnegative bisectional curvature to complete positive factors, flat
  factors, and compact symmetric factors" is slightly loose: CCZ's displayed
  conclusion is an alternative whose factor clause says each nonflat factor
  "admits a Kähler metric with bounded and positive bisectional curvature". The
  candidate's next sentence (combination with source338 pays the bounded subclass)
  is the accurate statement; the first clause could be aligned with it.
- O2. fixed-time-factorization.md could note explicitly that CCZ define P on ALL
  nonzero ordered pairs (their survey lines ~750–783) and prove the reaction
  inequality there, so the stabilizer twirl fills a gap relative to the displayed
  orthonormal-pair rotation in Gu/CCZ, not relative to their framework. This
  strengthens, not weakens, the attribution.
- O3. comparison.md could record that the n=1 case of the full target is also
  classical independently of source338 (Cohn–Vossen/Blanc–Fiala–Huber, which
  source338's introduction cites); this affects no quantifier.
- O4. When a manuscript stage is reached, the reliance on Mok Prop 1.1 content
  (H>0 at positive times) should cite Mok [69] alongside Gu/CCZ, since Gu obtains
  that point from Mok rather than re-proving it.

## My actual reading limits

Read in full: author candidate.md, scope-status.json, completion.json,
nonnegative-flow-bridge.md, local-null-propagation.md, fixed-time-factorization.md,
comparison.md, reading-limits.md, mechanism-checkpoint.md, verify.py,
check_interfaces.py, MANIFEST.json, source-receipts.json, primary-receipts.json,
interface-results.json, README.md; campaign criteria NEW-TEN-2026-10-14.md
(T338N-relevant sections plus the accepted-results and review-precedent passages;
the file is 1773 lines and was read via targeted sections, not sequentially);
AGENTS.md; parent intake.json, dispatch-r1.json, contribution-r1-brief.txt.

Source338 (private pinned blobs, hash-matched): introduction.tex all 258 lines;
preliminaries.tex all 479 lines; flow.tex lines 1–298 plus targeted greps over
300–878 for curvature-sign use-sites; charts.tex lines 1–230 and 325–369; discs.tex,
variation.tex, ellipsoids.tex by targeted grep for strict/positive/nonnegative
curvature use-sites only, NOT full reads; dynamics.tex and uniformization.tex not
read (main theorem applied at original hypotheses). bibliography.tex and main.tex
not read beyond grep hits for nonnegative-corollary claims (none found).

Primaries (packet private texts, hash-verified by the author verifier run):
ni-tam.txt lines 75–174 (Thm 0.1–0.3 statements), 1465–1539 (Lemma 4.1/4.2),
1770–1879 (Thm 4.2 statement and proof, Remark 4.1); survey.txt (Cao–Chen–Zhu)
lines 255–271, 628–1076 (Thm 2.7 Mok statement, Thm 2.8 statement and full
displayed proof, Yau-conjecture remark), references block; gu.txt all 357 lines;
brendle-schoen.txt lines 1–245 (Props 1–2 and proofs, start of Section 3);
liu.txt lines 1–150 (Thm 1.1 statement and strategy). Not read: Berger 1955 body,
Beauville body, Ni–Tam Thm 3.1 proof (the heat-deformation maximum principle),
Mok's original paper, original de Rham. These are accepted as named dependencies
exactly as the candidate declares them; the candidate's reading-limits.md is
consistent with what I could cross-check.

Web searches (2026-10-18, 3 queries, results logged in checks-receipt.json):
general nonnegative-bisectional uniformization status; the pinned source338
preprint and possible follow-ups; unbounded-curvature Kähler–Ricci flow literature.
Search snippets used as navigation only; no snippet was treated as a proof or as
an exclusion of worldwide priority.

I did not read the parallel proof-review directory and infer nothing from it.

## Integrity and provenance

- All nine external anchors recomputed byte-identical (sha256sum), 2026-10-18.
- Author verifier run once with the externally supplied anchor and the workspace
  preprints-tree: PASS_IDENTITY_ONLY (16 public files; canonical membership and
  private source/primary hashes verified by that script). Its known
  exact-inventory limitations are noted in the brief; this review does not treat
  integrity output as mathematics.
- This review directory is sealed by MANIFEST.json (SHA256 over every regular
  payload file) and verify_review.py, adapted read-only from the author packet's
  verify.py (helper provenance: author's verify.py, sha256
  902bd1800db5ad02e04c2efc9a0ac2afd632ea2400f8db5f5c7a75a81a002997, same
  anchor/membership/link-rejection design, with review-specific status fields and
  an added tree-wide symlink/nonregular-file rejection). Positive and
  reason-checked negative controls were run on copies under /var/tmp; results in
  checks-receipt.json. No checksum or finite check in this review certifies any
  mathematics.
- The external seal hash (SHA256 of this directory's MANIFEST.json) is reported in
  the reviewer's final message, outside the sealed tree.
