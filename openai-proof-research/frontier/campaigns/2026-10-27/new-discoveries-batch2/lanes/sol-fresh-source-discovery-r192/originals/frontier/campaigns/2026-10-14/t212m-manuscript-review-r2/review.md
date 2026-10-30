# T212M manuscript review, round 2: AH changed-hypothesis proof interfaces

Verdict: **PASS_AH_PROOF_INTERFACES_T212M**

REQUIRED: none.

Scope of the verdict. This round completes exactly one boundary: the operative
proof bodies of Ahlberg–Hoffman arXiv:1609.02447v2 Sections 6, 7 and 10, which
round 1 (seal c7942e07…3a99, PASS_FULL_MANUSCRIPT_T212M) explicitly did not
read, although manuscript Section 8 (08-use-sites) declares these sections
proof-level reuse under failed standing hypotheses AH A2(v) and A2(vii). Every
reuse found in those proof bodies is justified by a replacement actually
present in the frozen manuscript. This verdict has force only in conjunction
with the prior gates (proof-r1, contribution-r1, formal-review-r1,
manuscript-review-r1); it does not reopen them, does not audit the upstream
truth of S, AH or DH, and makes no acceptance, count (16/20 stands),
publication, staging or commit decision.

## Inputs and authentication

- Frozen manuscript anchor rechecked: `t212m-manuscript-v1/manifest.json`
  SHA256 = c71b20126326de8eab4d016b92cca78c9e43440653361899a8335fc2747c7b3f;
  package verifier returned PASS_IDENTITY_ONLY (46 payloads, 5 directories,
  pdf f6204f18…e13). All eight section hashes match `checks.json` here.
- Primary text: `fresh-analytic-discovery-r74/private/ahlberg-hoffman-v2.txt`
  SHA256 = f76794769284b94793095ee4b99a84ab1acb6b5cffa5509fc60141f742ecd4af,
  4048 lines. It stays in its git-ignored private location; no primary body is
  copied here.
- Prior reports read in full: manuscript-review-r1 `review.md`,
  `reading-limits.md`, `checks.json`, `verify.py`, `controls.py`; parent
  `manuscript-r1-adoption.json` (closure-pending paragraph is exactly this
  round's task). Round 1 read AH lines 255–983 and 1555–2712; this round read
  the complement actually at issue plus interface context (ranges below).

## Lines actually read in AH v2 (statement/proof distinction)

New operative proof reading, line by line:

- 942–1338: Section 6 complete (6.1 ordering; 6.2–6.4 flows, Voronoi
  averaging, subsequential limits, Lemmas 6.1–6.3 with proofs; 6.5 global
  labeling, Lemma 6.4, Proposition 6.5 with proofs; 6.6 constant labels;
  Lemmas 6.7–6.8 with proofs; 6.7 multiplicity, Lemma 6.9 + Claim 6.10,
  Lemma 6.11 with proofs).
- 1340–1552: Section 7 complete (Definition 7.1; trapping picture 1357–1385;
  Proposition 7.2 statement 1394–1405 and proof 1457–1552 including Claim 7.6;
  Lemmas 7.3–7.5 with proofs 1408–1455).
- 2679–3085: Section 10 complete (Theorem 10.1; Lemma 10.2; Remark 10.3;
  Theorem 10.4; Lemmas 10.5–10.7; Theorems 10.8–10.12; Remarks 10.13), every
  proof included. 2640–2678 (end of Proposition 9.13) and 3086–3103 (Section
  11 opening) read to fix the boundaries; Section 11 is not a dependency of
  Section 10 (line 314 states the two are independent), so its bodies were
  not read.

Interface re-verification reads (round 1 had already read these in full; I
re-read the operative parts to audit the interfaces myself, not to redo the
gate): 160–254 (Section 2 definitions: Dir, T0, random coalescing geodesic
Definition 2.3, Busemann (2)); 319–475 (A1/A2 at 326–354, Remarks 3.1–3.3,
shape theorem, Proposition 3.4 with proof); 479–563 (measurability note,
Section 4 statements); 564–741 (proofs of Lemma 4.1, Propositions 4.2–4.5;
Lemma 4.6 at 649–671 relied on from round 1); 743–824 (Section 5: Theorem 5.1
DH recap, Theorem 5.2 statement).

Manuscript files read in full this round: `02-cap.tex`, `03-metric.tex`,
`04-reference.tex`, `05-labels.tex`, `06-splice.tex`, `08-use-sites.tex` (the
03–06 mandate plus the use-site table and the cap facts it cites).
`01-scope.tex` and `07-finish.tex` are outside the AH-interface scope and are
relied on from round 1, which read them in full; nothing in AH 6/7/10
interfaces with them beyond what Section 8 already maps.

## What Sections 6, 7, 10 actually use (hypothesis inventory)

A keyword sweep for energy/resampling/independence language over the whole
text, then line-by-line confirmation inside 942–1552 and 2679–3085: the only
finite-energy or iid-resampling steps in AH are Lemma 8.6 (A2(vi)–(vii),
lines 1676–1736, "uniform downward finite energy" at 1713), the upward
finite-energy modification couplings of Section 9 (1952; the 9.2 coupling
2158–2172; the 9.10 wall 2485), and the DH existence input Theorem 5.1.
Sections 6, 7 and 10 contain no edge modification, no resampling, and no use
of independence among the edge weights ω. AH's own Remark 3.2 (374–376)
corroborates this: only Lemma 8.6 uses (vi)–(vii).

The operative inputs of Sections 6, 7, 10 are exactly: translation invariance
and ergodicity of the base law (pointwise ergodic theorem, including averages
over the auxiliary Voronoi cells and density-of-sites arguments); square
symmetries (rotation of the four reference geodesics; Case 2 of Proposition
7.2); the shape theorem and extended shape Proposition 3.4; unique passage
times (finite-geodesic uniqueness, tree property, connected intersections);
measurability/compactness/Portmanteau on the product space Ω1 × Ω4 with
independent auxiliary uniforms ξ; the four reference geodesics Γ0–Γ3
(existence via Theorem 5.2, i.e. via DH under full A2 including (v)); and the
Section 8/9 structural conclusions (Theorem 8.1, Lemma 8.8, Theorem 9.1,
Proposition 9.12–9.13) already covered by round 1 with their replacements.

Each of these is available for the cap law s in the manuscript: stationarity,
per-shift mixing (hence ergodicity) and Z² symmetries (02-cap Lemma 2.1);
shape and extended shape (03-metric Lemma 3.1, equation eq:extended, whose
derivation matches the structure of AH's own Proposition 3.4 proof, which
itself uses only the shape theorem and the ergodic theorem); unique passage
times (02-cap 46–50, with the correct non-frozen-V_e no-tie argument);
independence only between the cap field and auxiliary variables, which the
manuscript retains by construction (05-labels 8–10, 06-splice 14–18); the
four reference families (04-reference 167–194, replacing Theorem 5.2's
DH-with-finite-energy existence by D + W + the proofs of AH 5.3–5.6); and
the Section 8/9 conclusions (05-labels replacements, settled in round 1).

## Proposition-by-proposition interface audit

Ingredients are coded: ST stationarity, ERG ergodic theorem use, IND
independence (auxiliaries only unless noted), FE finite energy, UNI unique
passage times, REF four reference geodesics, SEL selector/label continuity
from Section 8, COA coalescence, Q quantifier structure. "Replacement" names
the manuscript location that supplies any ingredient AH obtains from a
failed hypothesis.

### Section 6 (labeling)

- Setup 942–955 (four Γ_i from Theorem 5.2 + rotations). REF via AH Theorem
  5.2, whose proof chain (5.3–5.6 over Theorem 5.1 = DH) uses full A2
  including upward finite energy for DH coalescence. Replacement: 04-reference
  167–194 (D lifted coupling, W cubic wall coalescence, AH 5.3–5.6 proofs
  reused, four square rotations). Distinctness of the four: distinct rotated
  tangent functionals plus AH Proposition 4.4 (its boundary step 4.6 applies
  to the cap by finite-mean coordinate/zigzag boundary routes and boundary
  ergodicity, 04-reference 179–182). Labels 0,1/4,1/2,3/4 by symmetry
  (1270–1271): square symmetry only. Justified.
- 6.1 ordering (956–978). ST, UNI, COA of Γ?; deterministic geometry.
  Justified.
- Lemma 6.1 (1002–1014). Pure auxiliary percolation (ξ only) + Borel–Cantelli.
  Justified.
- Lemma 6.2 (1058–1072). ST: ν_i shift invariance from invariance of P × Leb
  and covariance of the construction; no iid of ω. Justified.
- Lemma 6.3 (1073–1142). ST, IND(aux), compactness/Portmanteau on closed
  events; ω-marginal of ν_i is the base law. Justified.
- Lemma 6.4, Proposition 6.5 (1155–1176). Measurability, monotone
  convergence, order consistency. Justified.
- 6.6 constant labels (1191–1202). ERG on the joint (ω, ξ) shifts; cap mixing
  + iid ξ supplies joint ergodicity. Justified.
- Lemmas 6.7–6.8 (1203–1268). ERG over the random equivalence classes
  V_i(0) (1216–1220), Lemma 6.1 growth, Portmanteau closure (1225–1233,
  1259–1262). Interface needs: joint stationarity/ergodicity of (s, ξ) and
  the cells from the independent auxiliary construction. Justified; no
  independence among cap edges is used, matching 05-labels 9–10 and
  08-use-sites 26–29.
- Lemma 6.9 + Claim 6.10 (1274–1315). Deterministic flow mass bound 4^{−k}
  (1287–1297); transport scaling to P(0 ∈ A_i) (1299–1301) uses joint
  stationarity only; Portmanteau (1306–1315). Justified.
- Lemma 6.11 (1319–1338). Lemmas 6.8–6.9 only. Justified.

### Section 7 (central geometric argument)

- Trapping 1357–1385: UNI + compactness. Justified.
- Proposition 7.2 proof (1457–1552). Case 1: finite-visit event B_m from
  deterministic Dir(Γ_i) (Proposition 4.3) and Arc width < π/2 geometry;
  ERG density in H∆H′ (1474). Case 2: shape square or diamond, "rotational
  invariance" (1511) = square symmetry; Claim 7.6 (1527–1542) uses
  Proposition 3.4 extended shape — supplied for the cap by Lemma 3.1
  (eq:extended); ERG density (1547). No FE, no IND(ω). Justified.
- Lemmas 7.3–7.5 (1408–1455). Proposition 7.2 + noncrossing + ordering;
  7.5 second statement via Lemma 6.11; footnote 8's 0-1 via coalescence +
  ergodicity. Justified. This matches 05-labels 11–13 ("planar trapping,
  ergodic density and extended shape").

### Section 10 (all-ray ergodic theory)

- Theorem 10.1 (2712–2722). Theorem 8.1 + Theorem 9.1 + Lemmas 6.11/8.13
  (prior gates). Justified.
- Lemma 10.2 (2729–2745). Label comparison, Lemma 8.8, Theorem 9.1.
  Justified.
- Theorem 10.4 (2754–2790). Propositions 4.4–4.5 + density of random
  coalescing geodesics (10.2). Not cited by the manuscript; audited, no FE.
- Lemma 10.5 (2795–2814). Deterministic planar Busemann comparison (first
  intersection u_k, monotonicity); Lemma 4.1 gives B_g for all g ∈ T0 on one
  event. Justified.
- Lemma 10.6 (2822–2860). Lemma 10.5 + Proposition 4.2 limits along (y_k) +
  Proposition 4.4 strictness; rotational symmetry in the four-geodesic case.
  ρ_G = E[B_G(0,·)] is a cocycle expectation over the base shifts; cap
  ergodicity suffices (no extension ergodicity is needed here; the possibly
  non-ergodic lifted extension is confined to AH 9.2 and is handled by
  manuscript Lemma 3.2, 03-metric 70–109). Justified.
- Lemma 10.7 (2863–2889). Proposition 3.4 + per-pair Proposition 4.2
  linearity + finite net v_1,…,v_m; conclusion for every g ∈ T0 between the
  pair via the deterministic Lemma 10.5 comparison. Q: per fixed pair, then
  countable. Justified.
- Theorem 10.8 (2896–2908). Presence of every tangent functional cites
  Theorem 5.2 — under the cap this is replaced by 04-reference 167–173, which
  constructs G_ρ for each explicitly quantified tangent ρ; closure uses
  Lemma 10.6 monotonicity, Theorem 8.1 (limit selector exists; SEL), Theorem
  9.1 (it is a random coalescing geodesic), and expectation continuity of ρ
  at the limit. Justified with the replacement in place.
- Theorem 10.9 (2912–2962). The all-ray Busemann linearity. Nested finite
  families F_n built from the countable complement intervals of C*; estimate
  (31) per consecutive pair via 10.2/10.6/10.7 and the isolated/dense
  dichotomy; (33) holds for all g ∈ T0 simultaneously on one full event by
  the union bound over countably many n and pairs; Dir(g) ⊆ Arc(ρ_g) from
  Lemma 4.1 + shape. Q exactly as the manuscript claims. Justified.
- Theorem 10.10 (2976–3012). (a) all pairs g ≤ g′ via Lemma 10.5 + 10.9 and
  the eight-sector reduction; (b) the possibly uncountable family G is
  sandwiched between consecutive finite F_n members by order monotonicity
  (3002–3007), so no uncountable intersection of null events occurs; the
  final step is a countable union over n (3010); (c) C(ω) = C* a.s.
  Justified.
- Theorem 10.11 (3016–3039). Per fixed ρ ∈ C*: uniqueness from 10.10(a) and
  the neighbor/dense choice; countable union over v ∈ Z². The null set may
  depend on ρ — the manuscript states this dependence explicitly
  (05-labels 168–170). Justified.
- Theorem 10.12 (3044–3077). 1-1 correspondence via Proposition 4.4 +
  Theorem 9.1; M* proved at most countable first (disjoint open intervals
  between neighboring pairs, 3061–3068) and only then quantified almost
  surely (3069–3075). Justified.

### Cross-check of the manuscript's all-ray claims against AH 10

05-labels 157–174 (sec:allray): "deterministic closed set C dominated by μ"
= Theorem 10.10(c) + supporting-functionals bound ρ ≤ μ (Proposition 4.3,
line 613); "on one event every cap ray p has B_p with B_p(0,x) = ρ_p(x) +
o(|x|), ρ_p ∈ C" = Lemma 4.1 + Theorem 10.9(33); "limiting directions in the
contact arc" = 10.9 final paragraph; "uniform all-ray cone bounds from
countably many finite reference nets, not an uncountable intersection of
fixed-ray assertions" = the F_n construction verified above; "for each fixed
functional a unique coalescing, backwards-finite family; its null set may
depend on that functional" = Theorem 10.11 (fixed ρ) + Proposition 4.5 whose
mass-transport trifurcation proof (728–741) uses only unique passage times
and ergodic density, no energy; "presence of every tangent functional uses
the explicitly quantified construction of Section reference" = the verified
replacement of the Theorem 5.2 citation inside Theorem 10.8. The 08-use-sites
row "AH 9.1, 9.12–9.13; Section 10 … countable label approximations …
fixed-label null events are not silently intersected over an uncountable
random set" (56–60) is accurate: every uncountable-looking quantifier in
Section 10 is resolved by finite-net monotonicity or by a proved countability
(M*) before any almost-sure quantification.

### Cross-check of the remaining Section 8 rows touched by this round

- "AH 6.1–6.7" (08:26–29): confirmed — auxiliary partitions/labels use
  independent auxiliary randomness, stationarity, shape, finite uniqueness
  and the four reference families; independence of cap edges is genuinely
  unused.
- "AH Section 7" (08:30–32): confirmed — references, planarity, uniqueness,
  measurability, shape; no edge resampling occurs anywhere in Section 7,
  consistent with 05-labels 13–14.
- 05-labels 7–14 summary of Sections 6–7: accurate, including "These
  arguments introduce no edge resampling. The one downward operation occurs
  in AH 8.6." (verified: the sole (vi)–(vii) use in AH is Lemma 8.6).

## Binding prior requirements

- Contribution R1/R4: this round discharges the remaining "proof-level reuse
  under missing energy" reading for AH 6–7 and AH 10; D/S/P/W findings of
  round 1 are relied on unchanged. No new finite-energy or iid dependence was
  found in these bodies, so no full-target gap emerges; nothing weakens the
  round 1 verdict.
- The five round 1 optional editorial suggestions remain optional; this round
  found no actual necessity. No manuscript bytes were modified; no author
  amendment was made or is required.

## Trust and independence

No nested agents. No frozen-author file edited; the only files written are in
this round's own directory, plus disposable control copies under /var/tmp.
Nothing staged, committed, uploaded or published; no shared ledger touched;
no acceptance or count judgment (16/20 stands). Upstream truth of S, AH, DH
accepted as stipulated/primary input per AGENTS.md; the audit here is the
interface between AH's proof steps and the cap law's verified properties.
Checksums and the identity verifier certify bytes, not mathematics.
