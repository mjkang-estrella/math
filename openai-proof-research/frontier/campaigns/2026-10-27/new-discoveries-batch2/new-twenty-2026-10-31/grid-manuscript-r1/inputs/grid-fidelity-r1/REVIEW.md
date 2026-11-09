# Independent formal-fidelity review of MathDB 343536

This is an independent review, not acceptance. Root decides acceptance and credit.
Target: `GridFinal6.mathdb_343536`, packet SHA-256
`a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953`.
All paths below are relative to the campaign directory unless prefixed
`packet/`, which refers to this lane's fresh extracted copy.

## A. Definition and statement fidelity — PASS

The primary source used is the cached arXiv v2 text
`expanded-corpus-r131/sources/1908.05797v2.txt`. Its partition order is stated at
lines 111–116, Definition 5.1 at 263–267, lattice existence at Proposition 4.5
(line 196) and Example 5.3 (272–273), the natural action and free-vertex remark
at 282–286, and Conjecture 5.6 at 293–294 and 308–313. The raw MathDB record,
`expanded-corpus-r131/raw/343536.jsonl:1`, reproduces the same three sentences.
The v1 text has the same conjecture at 299–305.

* `packet/src/GridBasic.lean:13` defines G as Mathlib's literal
  `(pathGraph m).boxProd (pathGraph n)`, on `Fin m × Fin n`.
  Lines 83–90 prove its adjacency is one unit in exactly one coordinate.
  There is no toroidal edge, diagonal edge, or graph surrogate.
* `GridBasic.lean:15–17` counts `{x // G.Adj u x ∧ r x w}` for every
  representative w and every r-related u,v. Since every setoid class has a
  representative and these sets are finite, Nat.card is the ordinary
  neighbour count in that cell. Duplicate representatives do not strengthen
  the condition. `GridNeighbours.lean:8–40` proves the equivalent multiset
  formulation with multiplicities retained.
* `GridBasic.lean:19–20` makes EqPart precisely the subtype of equitable
  setoids. Its inherited order is relation inclusion, hence finer ≤ coarser.
  The discrete partition is bottom. `GridLattice.lean:15–46` supplies an
  unconditional complete lattice on this order: joins are setoid joins;
  meets are joins of equitable common refinements. In particular this is
  not a claim that the ordinary setoid meet remains equitable. Subgroup has
  its usual inclusion order.
* `GridBasic.lean:22–29` defines orbitSetoid by an actual element of a
  subgroup of the full `G ≃g G` taking u to v. This is the natural evaluation
  action, not an abstract isomorphic group acting by another representation.
* `GridBasic.lean:31–32` says some vertex is fixed only by the identity
  in the full graph automorphism group. This is exactly a trivial stabilizer.
* `GridFinal6.lean:7–15` is literally the requested conjunction, for every
  natural m,n with 1 ≤ m and 1 ≤ n. The exceptional formula means exactly
  2×2 and 3×3. Positivity includes 1×1 and all paths and excludes empty grids,
  where a free vertex does not exist and sentences 2 and 3 would fail.

An order isomorphism `≃o` between these lattices automatically preserves
least upper and greatest lower bounds; a separate preservation field is not
missing. The endpoint's Nonempty order-isomorphism assertion is the abstract
reading of “lattice isomorphic.” The source's surrounding discussion also
suggests the natural map Φ(H) = orbit partition. Both readings are covered:
`GridBasic.lean:49–81` defines Φ and proves monotonicity and order reflection
at a free vertex; `GridFinal.lean:22–36,64–70` exposes NaturalLatticeIso and
its iff. Substituting the three proved obligations gives this stronger natural
statement unconditionally for positive sizes. The exceptional theorem rules
out even a bijection, so it does not merely show Φ is non-injective.
This resolves the natural-map concern in `grid-review-r1/REVIEW.md`,
section A and section E, recommendation 1.

No vacuous premise, quotient by graph isomorphism, replacement subgroup lattice,
or weakened first sentence appears in the endpoint.

## B. Proof structure — PASS

The dependency trace is as follows. These are proved declarations, not assumed
source results or unresolved Prop arguments.

1. `GridFinal6.lean:15` applies `GridFinal4.mathdb_343536` to
   `main_orbit_proved`. `GridFinal4.lean:17` supplies
   `free_classification` and `exceptional_no_iso` to the original endpoint.
   `GridFinal.lean:48–62` proves the three sentences from these obligations.
2. MainOrbit's exact definition is `GridFinal.lean:8–10`: every equitable
   setoid equals the orbit setoid of its actual Hpi subgroup. Hpi
   (`GridSymmetry.lean:36–47`) consists of the A0 symmetries preserving
   every cell, not merely permuting cells.
   `GridOrdinaryBorder.lean:69–70` supplies MainOrbit via
   `main_orbit_of_ordinary_border`.
3. `GridFinal5.lean:38–59` performs exhaustive dimension cases: either
   dimension 1; 2×2; 2×n or n×2 for n ≥ 3; 3×3; remaining m,n ≥ 3.
   Paths use `GridOrbitPaths.lean:109–170` and transposition
   (`GridTransposeGroup`). Ladders use
   `GridLadderOrbit.lean:26–151`: matching corner partners, explicit
   reflections, transported row determinism and positive layers.
   Exceptional orbit witnesses use the complete finite classification and
   kernel-decided sym8 witness tables in `GridOrbitSmall.lean:20–46`.
4. The remaining geometric obligation
   `OrdinaryBorderTransitivity` (`GridFinal5.lean:33–36`) is discharged by
   `GridOrdinaryBorder.lean:62–66`, in fact without needing its exclusion
   of 3×3. The corner case is
   `GridCornerColors.lean:54–103`; the non-corner case is
   `GridOrdinaryBorder.lean:38–59`.
   `GridColorTiming.lean:39–90` propagates matching side colours and proves
   equal side lengths by first-corner degree separation.
   `GridSideAlignment.lean:9–87` propagates backwards to align positions
   and corner flags. `GridInternalFlags.lean:10–55` explicitly reverses
   the target chart when necessary, and `GridBorderFrames.lean:9–87`
   supplies actual reflection frames and the needed square transposition.
   Colour-flag agreement implies Hpi membership by
   `GridColorFlags.lean:58–66`.
5. There is no unproved WLOG bridge:
   `GridOrdinaryBorder.lean:7–35` proves transpose/reflection transport
   and A0 conjugation membership; `GridTransport.lean:7–42` fixes the
   inverse direction of transported partitions.
   Positive layer propagation `GridPropagation.lean:19–49` explicitly
   assumes positivity and uses a unique predecessor; all concrete
   hypotheses are proved in `GridOrdinaryLayers.lean:8–136`.
   The border restriction is literal and preserves equitability only for
   saturated sets (`GridBorderWalk.lean:9–40`). It retains isolated
   outside vertices without permitting inside/outside cell mixing.
   `GridBorderWalk.lean:55–93` and `GridColorTiming.lean:68–73`
   explicitly require/prove non-backtracking. Repeated colours remain valid.
6. FreeClassification is proved independently of MainOrbit in
   `GridFreeClassification.lean:68–86`: paths, degree-separated ladder
   flags, nonsquare corners, and near-corners in squares of side ≥ 4.
   `GridSideRigidity.lean:42–113` proves flag rigidity and equal side
   lengths in the full automorphism group. Negative exceptional cases are
   the explicit nonidentity stabilizer witnesses in `GridChecks.lean`,
   including the anti-diagonal reflection at both off-diagonal 3×3 corners.
7. ExceptionalNoIso is `GridExceptional.lean:15–24`.
   `GridFiniteCodes.lean:22` classifies all four-point setoids.
   `GridExceptionalPartitions.lean:30` classifies 3×3 equitable setoids
   by their corner and edge restrictions using degree invariance.
   `GridExceptionalCounts.lean:21–36` and
   `GridExceptionalCountTwo.lean:8–23` give upper bounds 9 and 7.
   `GridExceptionalSubgroups.lean:23–61` constructs ten distinct actual
   full-Aut subgroups using checked multiplication/inverse tables.
   Cardinality therefore contradicts an abstract isomorphism.
8. The complete lattice instance is independent of MainOrbit
   (`GridLattice.lean:15–46`). Surjectivity of Φ follows from MainOrbit
   (`GridFinal.lean:26–31`); its natural order isomorphism uses the
   free-vertex order-reflection proof in `GridBasic.lean:59–81`.

The Prop definitions retain historical “unsolved” comments, but every obligation
used at the final endpoint is discharged. The formal argument does not need a
separate theorem identifying the entire full automorphism group with A0.

## C. Independent semantic sanity — pending final logs

The review's new `scripts/enumerate.py` does not reuse the earlier review's
enumerator. It enumerates all restricted-growth partitions inside each degree
class, then checks Definition 5.1 directly. This pruning is complete: summing
neighbour counts over all cells forces related vertices to have equal degree.
It separately enumerates every adjacency-preserving permutation by backtracking,
then every subgroup by closed subsets containing the identity. Thus the full
automorphism group is computed, without assuming the reflection description.
Finite nonempty multiplicatively closed subsets of a group are subgroups.

The generated `Sanity.lean` checks the enumerated label lists with kernel
`decide`, including distinctness, list sizes, and equitability. Its bridge
examples turn that condition into literal IsEquitable and endpoint orbit
existence. It also checks positive/negative free-vertex instances, both
exceptional abstract non-isomorphisms, the 4×4 free case, order direction, and
a non-equitable one-cell 3×4 partition. Full-list completeness outside the
exceptional cases is independently established by Python, not claimed as a
new Lean cardinality theorem. These finite checks are diagnostics, not a proof
of the quantified theorem.

## D. Bounded formal spot check — pending final logs

All build artifacts are in `packet/build`; temporary/cache files are in
`packet/tmp`. The packet's inspected `scripts/run.sh`, `watch.pl` and
`lean.sh` enforce process-group RSS ≤ 6 GiB, taskset to CPUs 30,31, CPU
120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2 and Lean flags
`-j1 -M3500 -DwarningAsError=true`. The driver is strictly serial.
The upstream package paths are read-only inputs, not build destinations.
Only the missing Bound.Attribute artifact is compiled into the local tree.
The pinned mathlib detached HEAD and formal/lake-manifest.json both record
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The independent comment/string-aware scanner `scripts/scan.pl` scanned all
47 packet modules for sorry, admit, axiom, unsafe, partial, native_decide,
ofReduceBool, implemented_by and extern; `logs/forbidden-scan.log` is empty.
The packet's imported compiler/tactic infrastructure contains upstream unsafe
and axiom declarations; this is distinct from the transitive axioms of the
proved theorem. The latter must contain only propext, Classical.choice and
Quot.sound. Full compiler/checker logs are retained under `packet/logs`.

This bounded review does not replace root's decisive fresh replay. Round 6's
disclosed development-audit/replay overlap (`RESOURCE-NOTE.md:1–8`) remains
a historical resource qualification, not a logical premise or an erased failure.

## E. Manuscript readiness — QUALIFIED_PASS

There is sufficient mathematical and formal material for a manuscript; there is
not yet a clean final manuscript established by this review. Required editorial
and disclosure fixes, for root's integration:

1. State the entire positive-dimension theorem in all three sentences:
   all equitable partitions are full-Aut subgroup orbit partitions; abstract
   lattice isomorphism iff a free vertex exists; a free vertex exists iff
   the size is neither 2×2 nor 3×3. Also state that in positive cases the
   natural orbit map itself is an order/lattice isomorphism.
2. Restrict the novelty claim to sentence 1 for m,n ≥ 2. Treat paths as known
   from Brito–Manoel 2026, the automorphism group as classical, and the
   lattice statement as a consequence. Preserve root's modest-significance
   qualification and the unresolved compact-graph prior-art channel.
   This review performed no new literature search.
3. Give Definition 5.1, the literal box product, the source refinement order,
   the full-group stabilizer, and the Setoid/count/multiset correspondence.
   Include the positive-layer, non-backtracking and conjugation hypotheses
   explicitly, plus the exceptional cardinality argument.
4. Replace the stale headline `grid-formal-r6/PROOF.md:4` claiming the Lean
   implementation is partial; consolidate historical boundary sections into
   clearly labelled history. `STATEMENT-CORRESPONDENCE.md:20–23` likewise
   needs a historical label before its “no unconditional endpoint” sentence.
   Later round-6 sections already supersede these claims, so these are
   presentation defects, not proof gaps.
5. Identify the endpoint, source archive hash, Lean/mathlib pins, strict
   compilation, explicit-module leanchecker checks, declaration/forbidden-token
   audits, allowed transitive axioms, independent finite checks, and root's
   separate decisive replay. Disclose the resource overlap from round 6.
6. State access limits honestly: this review read cached arXiv v1/v2 text and
   local records; it did not access the SIADS body, Brito–Manoel body, or
   Godsil body, and did not refresh public registries. The earlier review's
   abstract-only Brito–Manoel evidence and bounded compactness search must
   not become claims of exhaustive prior-art clearance. Correct the MathDB
   2018/unrelated arXiv:1807.10954 provenance if discussed; the source
   conjecture is arXiv:1908.05797 (2019; journal 2020).

No mathematical source-code fix has been identified. Manuscript cleanup,
candid limits, and root's independent acceptance/replay remain required.

## Input binding and scope

`inputs-before.sha256` and `inputs-after.sha256` bind all requested input
files, with individual absolute paths. The packet hash matches the brief.
Procedural disclosure: the initial round-6 document read occurred before the
first manifest was recorded; the manifest was established before extraction,
source review and builds. Thus the review cannot claim a before-first-read
binding for those round-6 prose inputs. They were never edited here.
Upstream Bound.Attribute source has its own before/after hash manifests.

No child agents, git commands, network, browser tabs, shared-ledger edits,
publication, uploads or external messages were used. All writes are lane-local.
Acceptance and discovery credit are explicitly reserved to root.

Additional replay diagnostic: the inherited Audit modules emit deprecated-import
warnings (for example `Audit3.lean:2536`, Lean.RBTree) even with the requested
warningAsError flag. Their processes return exit 0. “Strict” in this report
records the exact requested command flags and exit status, not absence of
diagnostic warnings. These are auditor/upstream import diagnostics; inspect the
retained logs when interpreting validation claims.

Reviewer-run interruption disclosure: the first long replay driver returned
exit 143 while compiling Audit6, after 46 modules including the endpoint had
compiled and passed leanchecker. Its detached timeout/Lean process group
survived the driver and watchdog. I verified its cwd was this lane's packet,
sent TERM to that process group, and excluded the interrupted Audit6 log from
certification. The RSS watchdog was absent between the driver interruption
and this cleanup, so perfect uninterrupted watchdog coverage is not claimed.
The inherited CPU/affinity/timeout/Lean memory settings remained on that
process. The final audit was rerun serially from the unchanged source,
with a fresh capped invocation; logs/replay-resume.log records the resumption.
No other lane's processes were signalled.
