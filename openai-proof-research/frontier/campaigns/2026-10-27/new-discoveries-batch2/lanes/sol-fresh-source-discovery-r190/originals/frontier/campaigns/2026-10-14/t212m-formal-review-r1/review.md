# T212M independent scoped formal review r1

Verdict: **PASS_SCOPED_T212M** (scoped deterministic support only).
This is NOT PASS_FULL_FORMALIZATION. No acceptance, count change (16/20 stands),
staging, commit, upload or publication follows from this review. The parent alone
decides acceptance. No parallel manuscript, proof or contribution review was read
or used to reach this verdict.

## Inputs and authentication

- Frozen packet: `../t212m-formal-v1/`. Externally supplied manifest anchor
  `cc09818fed56aa44deda1f8fb9baf6d018bf6d4c3f8317f7bb6612f31624ce00` was checked
  against the raw manifest bytes BEFORE parsing. Exact inventory: 17 files,
  directories `inputs`, `validation`; no symlinks, hardlinks or extras.
  `T212M.lean` 9fbbbbc1…a8c and `Controls.lean` 0b9ae501…d9ee match the dispatch.
  `inputs/binding.json` binds the same two sources and the r74 author anchors,
  with `full_theorem_formalized: false`.
- Frozen author candidate `../fresh-analytic-discovery-r74/`: manifest
  26a78331…9566 matches; `candidate-proof.md` a4fa6e43…b55 and the use-site
  `label-stability-interface.md` a11f472d…ea0 match their manifest entries.
- The packet's own `verify.py` passed with the anchor; its
  `integrity_controls.py` passed 15/15 (only the positive case accepted).
  Packet authentication was repeated after every mutation and at the end.

## Build (fresh, from sources)

Command (twice, each into a NEW /var/tmp directory):
`python3 -B rebuild.py --output /var/tmp/t212m-formal-review-r1-rebuild-1792343022`
and, inside `run_review.py`, `--output /var/tmp/t212m-formal-review-r1-xz7orbtm/builder-output`.
Result both times: exit 0, `PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS`,
14 support and 17 control declarations, empty `support.log` / `controls.log`
(no warnings). `Checks.lean`, `types-axioms.log`, both empty logs and
`receipt.json` are byte-identical to the frozen `validation/` copies
(receipt 978ece2b…03b4). Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52,
binary SHA256 e8baaa71…5550; nine pins match lake-manifest.json
(mathlib d13f23b723b8a846827a245b89c10fc7d3f11612); tracked dependency trees clean;
zero untracked non-ignored entries in all nine. Dependency cache fingerprint
(148428 entries, 13b9664e…d28d) identical before and after. No network use.

Trust boundary: the two packet modules (and my `Independent.lean`) are
elaborated and kernel-checked afresh. Cached Mathlib/dependency `.olean` files
and the compiler binary are TRUSTED, not rebuilt or re-checked (no lean4checker /
external kernel replay was run).

## Axiom and type audit

- Every one of the 31 declarations has its elaborated type printed (`#check`)
  and its axiom closure printed (`#print axioms`); I read every type in
  `builder-run/types-axioms.log` against the source. Each closure is a subset of
  {propext, Classical.choice, Quot.sound}; no `sorryAx`.
- Independent environment inventory (`Independent.lean` `#eval`, not regex):
  module `T212M` contains exactly 17 constants = the 14 audited declarations +
  `walkCost.eq_1` + two `late_segment_minimizes._simp_1_*` auxiliaries; module
  `Controls` contains exactly 34 = the 17 audited + 9 `eq_1` equation lemmas
  (including `T212M.changeBudget.eq_1`) + 8 `_proof_*` auxiliaries. All are
  `def`/`theorem`; no axiom, opaque, instance or unsafe constant; all closures
  standard. Hence no meaningful declaration is omitted from the audit.
- Source scan of both packet files: no `sorry`, `admit`, `axiom`, `opaque`,
  `unsafe`, `native_decide`, `implemented_by`, `extern`, `set_option`,
  `macro`/`elab`/`syntax`, `instance`, `attribute` or `@[`. The imported
  `Mathlib.Basic.Real.Basic` is a git-tracked file at the pinned mathlib revision.

## Mathematical semantics (read in full)

Notation: `walkCost w p = (p.edges.map w).sum` counts every edge traversal with
multiplicity (pinned by `rfl`). `changeBudget F w w' = Σ_{e∈F} |w' e − w e|`
(pinned by `rfl`). Weights are functions on all of `Sym2 V`.

Support (14):
1. `changeBudget` – the cost budget Δ, faithful.
2. `finite_cost_change` – for a finite SET S, |Σ_S w' − Σ_S w| ≤ Δ. Correct.
3. `walkCost` – multiplicity-counting walk cost, faithful.
4. `walkCost_append` – additivity under concatenation.
5. `walk_cost_change` – for an edge-simple walk (`edges.Nodup`) cost changes by ≤ Δ.
   Nodup is genuinely needed (reviewer `budget_needs_nodup`, author control).
6. `walk_cost_unchanged` – walks avoiding F have equal old/new cost.
7. `distance_dominated_by_cost` – from d u u = 0, triangle inequality and the LOCAL
   edge bound d u v ≤ w s(u,v) on adjacent pairs, derives d a b ≤ cost for EVERY walk.
   Verified; used by author and reviewer instances.
8. `detour_barrier` – for symmetric triangle d dominated by original walk costs,
   d x c ≤ C, calibration d x b = d x a + d a b, and an edge-simple walk a→b
   visiting c: new cost ≥ d a b + 2 d x a − 2C − Δ. Matches the prose toll
   T_s(a,b)+2T_s(x,a)−2C−Δ. Original nonnegativity is not even required here.
9. `late_segment_minimizes` – if each changed edge has SOME endpoint with
   d x c ≤ C, C + Δ/2 < d x a, the segment is an original geodesic (cost = d a b)
   and avoids F, then it is new-minimal among edge-simple competitors.
   Avoidance is a hypothesis HERE only; it is discharged in item 12.
10. `walkCost_nonneg` – nonnegative weights give nonnegative walk cost.
11. `calibrated_segment_avoids` – avoidance DERIVED from calibration, C < d x a,
    domination and original nonnegativity. Proof checked: a changed edge on the
    segment would put c with d x c ≤ C on it, forcing d x a ≤ C.
12. `ray_tail_stable` – intermediate main theorem. Hypotheses: arbitrary simple
    graph (possibly infinite), symmetric triangle d, nonnegative OLD weights,
    w' = w off finite F, domination of d by every old walk cost, indexed vertices
    `ray : ℕ → V` with given walks `segments i j` whose old cost is d for i ≤ j,
    calibration from x for i ≤ j, escape d x (ray n) → ∞, region bound C.
    Conclusion: ∃ N, every forward segment with N ≤ i ≤ j is new-minimal against
    every EDGE-SIMPLE walk. No new-weight nonnegativity is assumed (reviewer
    `edge_simple_instance_negative_weight` applies it with w' = −1 on F).
13. `bypass_cost_le` – Mathlib loop erasure (`Walk.bypass`, edge sublist) does not
    increase a nonnegative cost.
14. `ray_tail_stable_all_walks` – final main theorem: as 12 plus `hw'`
    (nonnegative new weights); conclusion against EVERY finite walk, via
    `p.bypass` (a path, hence edge-simple) and item 13.

No preservation conclusion is hidden in a hypothesis. The only hypotheses that
mention w' are `hoff` (finite support of the change) and, in 14, `hw'`.
Calibration, domination, segment cost and escape mention only w and d. Avoidance
and new minimality are conclusions. The region hypothesis is never restrictive
for finite F (reviewer `region_constant_exists`). No infinite path/ray object is
encoded: `segments` need not be coherent subwalks of one path, and walks for i > j
are unconstrained data. This generality is harmless for the conclusion.

Controls (17): `lineDistance`, `lineWeight`, `changedEdges`, `newWeight`, `segment`
(definitions on ⊤ over Fin 4, edge {0,1} lowered 1 → 1/2); `line_triangle`,
`line_dominates` (domination via item 7); `late_segment_example` (item 9 instance,
x=0, C=0, segment 2→3, Δ/2 = 1/4 < 2); `repeatedEdge`,
`repeated_edge_breaks_single_budget` (0→1→0→1 changes cost by 3/2 > Δ = 1/2);
`earlySegment`, `shortcut`, `early_segment_is_old_minimal`,
`early_segment_unchanged`, `without_lateness_minimality_fails` (unchanged old
geodesic 0→2 of cost 2 loses to 0→1→2 of new cost 3/2); `newWeight_nonneg`,
`late_segment_all_walks` (item 9 + item 13: all walks 2→3). Each statement was
read against its elaborated type and is correct as stated.

## Independent reviewer checks (`Independent.lean`, 60 reviewer constants, standard axioms)

- Statement pins: `changeBudget`, `walkCost` (by `rfl`), the cons rule, and both
  main theorems plus `detour_barrier` restated with explicitly written binders.
- Nonvacuity of BOTH main theorems on an infinite graph (⊤ on ℕ, d = w = |u−v|,
  x = 0, ray n = n, single-edge segments, F = {s(0,1)} with w' = 1/2 there; the
  changed edge lies on the ray, `half_change_genuine`). The author Fin 4 controls
  cannot instantiate items 12/14 since escape is impossible for bounded d.
- `uniform_late_segment_all_walks`: the use-site's ray-uniform form in METRIC terms
  (threshold C + Δ/2 in root distance, any calibrated geodesic segment, every walk)
  follows from items 9, 11, 13 with avoidance derived.
- Hypothesis deletions, each with every other hypothesis proved:
  `all_walks_needs_new_nonneg` (w' = −1 on F: back-and-forth loops make the conclusion
  of item 14 false for every N); `lateness_needed` (item 9 without lateness fails on
  the same graph); `budget_needs_nodup` (item 5 without Nodup fails).
- Region constant always exists for finite F: `region_constant_exists`.

Mutation controls on /var/tmp copies (all outcomes and reasons as expected; frozen
packet re-authenticated after each): builder rejects `sorry` in support, declared
`axiom`, `private axiom` dependency (rejected by the axiom audit, not the token
scan), `sorry` in controls, budget without absolute value, deletion of `hw'`,
deletion of lateness, wrong mathlib pin. A hidden-preservation hypothesis added to
item 14, and a conclusion weakened to edge-simple competitors, are ACCEPTED by the
builder but REJECTED by `Independent.lean`; exit 0 alone is therefore not evidence
of semantics. The three compile-failure cases are checked only by the builder's
coarse reason string. Numerical or concrete checks do not prove the theorems; the
kernel proofs do.

## Use-site comparison

Use-site: r74 `label-stability-interface.md` lines 110–133, "Tail existence under
any finite metric change", cited by `candidate-proof.md` line 250 ("explicit
cost-barrier lemma"). Matches: finite F, Δ = Σ|s'−s|, toll
T_s(a,b)+2T_s(x,a)−2C−Δ, threshold T_s(x,a) > C+Δ/2, unchanged avoiding
competitors, loop erasure with nonnegative weights. The formal region hypothesis
(one endpoint per changed edge) is weaker than "V contains all endpoints, C = max".
"After the last visit to V" is replaced by derived avoidance. Positive weights are
weakened to nonnegative ones.

Assumptions left OUTSIDE formal scope (application obligations):
1. Existence of a real-valued original passage time T_s on the graph (connectedness,
   finite infimum), with symmetry, triangle inequality and domination; setting
   d = T_s supplies items 12/14 hypotheses only when these hold.
2. Existence of an original geodesic ray from x; its vertices enumerated as `ray`,
   with subpaths as `segments` (and some walks for i > j); calibration follows from
   geodesicity along a ray from x and is not formally derived.
3. Escape T_s(x, ray n) → ∞ (coercivity, §4 of the candidate) for every relevant ray.
4. Nonnegativity of s and s' extended to all of `Sym2 V` (non-edges set arbitrarily
   nonnegative); finiteness of the change set F and of its endpoint distances.
5. The prose's UNIFORM cutoff over all old rays from x in index/prefix form
   ("V visited only within a uniformly bounded geodesic prefix") uses coercivity
   and is not formalized; only the metric threshold form is derivable.
6. Passing from "every forward finite segment of the tail is new-minimal" to "the
   tail is a new geodesic ray" needs coherence of `segments` (not encoded).
7. "Reverse the roles for the other direction": the theorem is symmetric in w, w'
   but needs new-metric existence, calibration, escape and region hypotheses for s'.
8. Everything else: cap construction/finite cap influence, original→cap comparisons
   (`tail-and-modification.md`, infinitely many changed edges, different argument),
   DH limiting coupling, random selectors, Busemann functions, limiting graphs,
   half-plane transfer, label/selector stability, cubic wall, mass transport,
   all-ray classification and the moment-free no-bigeodesic theorem itself.

## Findings

REQUIRED: none.

OPTIONAL (no effect on the scoped verdict):
- O1. Add an infinite-graph instance of `ray_tail_stable(_all_walks)` to the packet;
  current README/coverage wording ("meets the theorem hypotheses", "all-walk
  instance") concerns the segment lemma only, which a reader could misread.
- O2. Export a uniform metric-threshold corollary like the reviewer's
  `uniform_late_segment_all_walks`, which matches the use-site more closely than
  the per-ray `∃ N` statement.
- O3. State negative controls as hypothesis-deletion propositions and add the
  `hw'` deletion control.
- O4. Harden `rebuild.py`: its token scan misses `private axiom` (axiom audit still
  catches it), `set_option`, `macro`/`elab`, `attribute`; its cache check ignores
  untracked files; mutation reasons for compile failures are coarse.

## Reading limits

See `reading-limits.md`.
