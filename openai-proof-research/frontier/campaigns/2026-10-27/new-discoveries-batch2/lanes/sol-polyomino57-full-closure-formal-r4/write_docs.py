from pathlib import Path
import json,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,25));signal.alarm(30)
L=Path(__file__).resolve().parent
runs=[json.loads(s) for s in (L/'bench/runs.jsonl').read_text().splitlines()]
(L/'benchmark-results.json').write_text(json.dumps(runs,indent=2)+'\n')
(L/'GAPS.json').write_text(json.dumps(dict(full_endpoint=False,credit=0,root_owns_acceptance=True,counts={'additional':5,'total':35},closed_chain_through=7,remaining=['all-row finite closure 7→8→9→10→11','literal paths from every local target into its common target family','terminal family membership in actual checked placement forests, including translations/normalization equality','unconditional UniversalContainer 11 witness and downstream source negation/minimum-size upper bound'],not_impossible=True),indent=2)+'\n')
(L/'SUMMARY.md').write_text('''# Full closure attempt r4 — INCOMPLETE, credit 0

The requested unconditional `Polyomino57.UniversalContainer 11 Polyomino57.witness` is NOT delivered. The complete certified chain remains through seven. Neither the selected row benchmarks nor the Python layer counts establish closure of another layer. Root owns acceptance; counts remain 5 additional / 35 total.

Three immutable archives were SHA256-verified before extraction; see input-hashes.json. The archived strict replay.py, not the development replay, rebuilt every size-seven dependency: 56 modules / 1,371 actual-origin declarations, 173.11 seconds, peak sampled group RSS 2,496,040,960 bytes. Input archives were never edited. No active canonicalgeometryr2 source was read. No git, other-lane/shared edits, children, browser or external actions occurred.

First benchmark: the full literal size-eight target definition fits after the existing depth/heartbeat settings (16.08 seconds, 2,549,366,784 bytes). Three eight-row 7→8 modules, at source starts 0, 376 and 752, passed in 10.32, 15.19 and 29.99 seconds. Index position strongly affects kernel cost. The 95-module extrapolation is 16–48 minutes, not a measured full-layer runtime or a lower bound. All 760 source rows were generated, but only those 24 rows used the global array checker.

Concrete flat representation failures: size-ten and size-eleven literal target modules were killed by the prescribed group-RSS monitor, at 2,947,727,360 and 2,943,537,152 bytes, respectively, after about 4.4 seconds. The 45ms sampler can overshoot its 2800MiB trigger. These are representation failures, not impossibility evidence for the theorem. The initial size-eight default recursion-depth and size-nine default-heartbeat failures were elaboration limits, not false certificate checks.

Adaptation: FamilyAssembly removes the global-array requirement from semantic coverage. Each row may certify a small local array, provided every target has a proved membership in a common predicate family. FamilyTree supplies checked binary paths to small array leaves. Both keep placement translation-only. These are CONDITIONAL interfaces, not the missing finite proofs. The local benchmark generator checks indices and literal translated equalities for batches of 8, 32 and 128 rows at every remaining size; those benchmarks do not supply family membership. Detailed successful/failed run receipts and logs are retained.

A balanced size-eleven target experiment splits the entire generated target data into 2,048-row source modules, each containing 32-row leaves; tree/build.py records its actual resource outcome. This is an attempted response to the flat-array blocker, not a claim that balanced membership or terminal correspondence has been completed. Consult tree-build.log and benchmark-results.json for the final outcome. No external enumeration completeness or expected-count hypothesis appears in the new Lean interfaces.

The source packet contains only passing components and their fresh source dependencies, with strict extracted replay and actual-origin axiom/flag audit. Experiments and failures remain in the lane. There is no manuscript-ready endpoint; root must still obtain all finite closures and actual forest correspondence before manuscript/review acceptance.
''')
(L/'INTERFACES.md').write_text('''Namespace Polyomino57; exact types are emitted by the extracted actual-origin audit.

* `FamilyRowClosed B row`: exists a finite row-local next array and choice function; every local target satisfies B and the complete successorFastRowCheck succeeds.
* `family_growth_step`: applies the already proved represented_growth_step to one such local certificate and returns normalized equality to a B-member.
* `family_growth_coverage`: any family chain with singleton base and all local certificates covers every Grown input through the given depth. No finite family checks are assumed closed here.
* `universal_of_family_certificates`: derives literal UniversalContainer 11 witness from singleton base, ten complete family steps and actual terminal translated inclusions. These hypotheses remain mandatory.
* `RowFamilyTree`, `FamilyMember`, `familyLookup`, `familyLookup_sound`: a Boolean path selects a subtree; a nat index selects a row in a small leaf array. A successful lookup proves literal membership. Both bad paths and out-of-bound indices return none.
* `familyRowClosed_of_paths`: a checked row-local array plus successful paths for every one of its targets yields FamilyRowClosed for the common tree predicate.

The three Closure7C benchmarks have closed checker theorems using full layer8. Local{7,8,9,10}N{8,32,128} benchmarks have closed checker theorems using per-row target arrays; they do not have global target-family membership theorems. The terminal forests are not imported by the new component packet, hence their prior checked placements are not claimed freshly replayed here.
''')
(L/'RESOURCE-NOTES.md').write_text('''All Lean runs use byte-identical frozen run.py and pins.json: Lean4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, -j1, warningAsError=true, autoImplicit=false, CPU210/215sec, wall230sec, group-RSS sampling45ms and kill2800MiB. No parallel Lean builds or increased memory allowance. Data generation/packaging scripts set hard512MiBAS, BLAS1 where relevant, bounded CPU/wall; the complete Python layers used about156MiB peakRSS and about3seconds. Script supervisors use the frozen post-spawn allowance arrangement.

Failures retained: default depth at size8; default heartbeats at size9; prescribed RSS kills at flat sizes10/11; initial local certificate generator emitted an extra parenthesis and produced syntax/stuck-decide errors. The generator was corrected, failures preserved, and all local batches rerun. These failed syntax runs do not constitute mathematical counterexamples. benchmark-results.json records every run, including failures. The complete chain is not reported as extended merely because sampled rows pass.

The sampled local throughput is an estimate only. No proof of impossibility or cap-compliant complete enumeration proof is claimed. Exact binary-tree experiment outcomes and fresh packet receipts accompany this note.
''')
