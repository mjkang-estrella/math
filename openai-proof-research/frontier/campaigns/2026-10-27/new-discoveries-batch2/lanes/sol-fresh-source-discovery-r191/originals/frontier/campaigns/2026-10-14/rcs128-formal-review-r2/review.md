# RCS128 scoped formal support: independent review r2 (recovery of r1)

Reviewer prose: CC BY 4.0. Reviewer code (`checks/ReviewerControls.lean`, `scripts/*.py`, `verify.py`): MIT. Reviewer: fresh independent formal reviewer; I did not write any of the reviewed code. The r1 review was killed (`Killed: out of memory.`) before it reached a verdict. Its files are preserved unchanged in `../rcs128-formal-review-r1/` and were read only as unverified work in progress. None of the evidence below comes from r1.

## Verdict

**PASS_SCOPED_SUPPORT**, with reading and trust limits below. The verdict covers only the 16 frozen support theorems as stated. They are scoped finite combinatorial and scalar lemmas, correctly proved, with standard axioms only. Their hypotheses do not encode the target. coverage.json delimits them accurately apart from the optional findings O1–O7.

This is **not** a formalization of the full RCS128 theorem, nor of any string, graph, geometry, or algorithm statement. It is not acceptance of the candidate proof, not a proof-review PASS, and not a contribution or priority verdict. Count 12/20 is unchanged. The root alone accepts.

No required findings. Optional findings O1–O7 are listed below. O1 limits how the frozen `Controls.lean` may be cited.

## Objects reviewed (all hashes recomputed; all match the brief)

| Object | SHA256 |
|---|---|
| `fresh-structural-discovery-r37/MANIFEST.json` | `a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6` |
| `…/candidate.md` | `ebfed67a43a306af4788c39300e2a418f82193c826bae130508fd87955d39137` |
| `…/original-scope.txt` | `7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60` |
| `rcs128-formal-v1/manifest.json` (external anchor) | `c3a051864862ebf53c24fce85da991f2e1da18340d38afdae238f3a160361963` |

* `rcs128-formal-v1` contains exactly 14 payload files plus `manifest.json`, and 2 directories. All 14 hashes match the manifest.
* The frozen `verify.py` gives `PASS_IDENTITY_ONLY` with the anchor and `FAIL: external anchor mismatch` with a one-digit-changed anchor (`checks/frozen-identity.log`).
* Before execution I read RCS128.lean, Controls.lean, coverage.json, rebuild.py, verify.py, lean-toolchain, lakefile.toml, lake-manifest.json and all of `validation/final/`. I also read the whole of candidate.md and original-scope.txt. I made no changes to any frozen or author byte.

## Build, toolchain, trust boundary

**Compiler.** Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The lean binary SHA256 is `e8baaa71…5d5550`.

**Dependency pins.** All nine checkouts are at their locked revisions with clean tracked files (`checks/toolchain-and-pins.log`): mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, plausible `118aa17e…`, LeanSearchClient `ddf04cf3…`, importGraph `e928b725…`, proofwidgets `106ff4fa…`, aesop `355695d5…`, Qq `6a489d9a…`, batteries `f2effa3d…`, Cli `e92c9f15…` (Cli has no built lib). All git calls ran with `GIT_OPTIONAL_LOCKS=0`, so `git status` could not rewrite dependency indexes.

**Fresh source rebuild.** Command: `python3 -I …/rcs128-formal-v1/rebuild.py --output …/rcs128-formal-review-r2/checks/fresh-build --cache …/formal/.lake/packages --lean …/lean-4.34.1-linux/bin/lean`.

* It ran in a `systemd-run --user --scope -p MemoryMax=3G -p MemorySwapMax=0` cgroup under `timeout 540`. Peak RSS was 1.75 GB; wall time was 6.7 s. Status: `PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS`, 16 support and 7 control declarations.
* `types-axioms.log`, `Checks.lean` and `receipt.json` are **byte-identical** to the frozen `validation/final/` files. support.log and controls.log are empty: no errors or warnings.
* An earlier attempt under `prlimit --as=3GiB` failed before compiling anything: `lean::exception: failed to create thread`, because thread stacks count against RLIMIT_AS. It is kept in `checks/attempt1-rlimit-as/` and is not evidence either way. The cgroup memory limit replaced it.

**Reviewer build** (`scripts/review_build.py`, same cgroup, 180 s per step):

* It copies the two frozen sources after checking them against the anchored manifest, then compiles RCS128, Controls and `checks/ReviewerControls.lean` from source.
* It prints the type and axioms of all 59 reviewer declarations and rejects errors, warnings, nonstandard axioms, and the tokens `sorry admit unsafe native_decide implemented_by extern opaque axiom set_option macro elab syntax notation run_cmd run_tac`. None of these tokens occurs in the three sources.
* Result: `PASS_REVIEWER_BUILD_CONTROLS_AND_MODULE_KERNEL_REPLAY` (`checks/reviewer-build/receipt.json`).
* Axiom profile of the 59 declarations: 37 use {propext, Classical.choice, Quot.sound}, 15 use {propext, Quot.sound}, 7 use none.

**Kernel replay (module-only).** `leanchecker -v RCS128`, `… Controls` and `… ReviewerControls` each replayed the module's own constants against the imported environment and exited 0.

* **Limit:** there was no `--fresh` replay. Re-checking all imported mathlib constants was excluded by the memory policy, so dependency `.olean` files are **trusted read-only** and were neither rebuilt nor replayed. Fresh implementation and reviewer objects were compiled from source.
* **Hazard found:** the leanchecker source (`src/lean/LeanChecker.lean`) shows that with no module argument, including `--help`, it falls back to replaying every module on the search path in parallel. A 20 s probe with `--help` hung and was killed by its timeout; no process was left. The reviewer script always passes explicit module names. I did not establish whether this caused the r1 OOM.

**Copied-packet mutation tests** (`scripts/mutation_tests.py`, `checks/mutations*/summary.json`). Each case copies the frozen package, applies one mutation, runs the **copied** `rebuild.py` with `--cache`/`--lean`, and runs the copied `verify.py` with the original anchor.

| Case | rebuild.py result | verify.py |
|---|---|---|
| M0 unmodified copy | PASS | PASS |
| M1 false statement (`2k+3 ≤ δ(k+1)`) | FAIL: linarith error | FAIL |
| M2 drop `hfree` | FAIL: unknown identifier | FAIL |
| M3 deprecation warning only (Controls) | FAIL: warning rejected | FAIL |
| M4 `sorry` | FAIL: forbidden token | FAIL |
| M5 `private axiom` used inside a proof | FAIL, but only through an incidental unused-variable warning | FAIL |
| M5b same, after `clear` | FAIL, again only through the warning | FAIL |
| M5c `private axiom` used by a new theorem | FAIL: `unapproved axiom dependency: RCS128.cheat_use` (`depends on axioms: [RCS128.cheat✝]`); the regex misses `private axiom`, the `#print axioms` gate catches it | FAIL |
| M6 `native_decide` | FAIL: forbidden token | FAIL |
| **M7 weakened statement** (`output ≤ 4·optimum`) | **PASS** | FAIL |
| M8 Controls genuine error | FAIL: decide error | FAIL |

M7 is expected behaviour, not a defect in this packet. The harness certifies compilation and axioms, not *which* statement was proved; statement identity rests on the manifest hashes plus the human type audit below. See O2.

## Theorem-by-theorem audit (printed types read against the source and the candidate)

Each theorem is listed as: statement; where the candidate uses it; assessment. The types printed in `checks/fresh-build/types-axioms.log` match the source declarations exactly.

1. **`even_card_of_reflection`.** Statement: s, rho closed on s, involutive on s, fixed-point-free on s ⇒ `Even s.card`. Proof: card_bij between `x < rho x` and its complement.
   * Candidate use: §2, "reflection pairs occurrences … count is even".
   * Assessment: correct. Every hypothesis is necessary (controls `drop_free`, `drop_closure`, `drop_involution`). In the candidate, fixed-point freedom comes from the two **tagged** components T and rho(T) (§1) and from the τ-paired distinct walks (§2). `note_untagged_central_occurrence_is_fixed` and `pos_tagged_components` show why tagging matters. Lean does not construct either.
2. **`even_phase_card`.** Statement: as (1), plus `P x → P (rho x)` on s ⇒ the phase count is even.
   * Assessment: correct. One-directional preservation suffices because rho is an involution. Phase preservation is necessary (`drop_phase_preservation`). An even total does not give an even phase count (`drop_phase_total_parity`).
3. **`filter_eq_range_at_boundary`** and 4. **`adjacent_pair_of_even_tail`.** Statement: a downward-closed P on `range n` with an even filter count ⇒ `P(2i) ↔ P(2i+1)` for `2i+1 < n`.
   * Assessment: correct, and pairing is from the top: index 0 is the largest exit.
   * Necessity: downward closure (`drop_downward_closure`), even tail (`drop_even_tail`), the index bound (`drop_index_bound`), and alignment of pairs at even indices (`drop_pair_offset`: offset pairs are not controlled).
   * This matches "pair adjacent sorted layers from the top". Because it applies to every pair of the full list at once, the candidate's induction by top-pair removal is not needed for agreement.
5. **`adjacent_exit_threshold`.** Statement: antitone `z` on indices `< n`, phase `b ≤ z a`.
   * Assessment: correct. This is the candidate's EXIT convention, with count = #{i : z_i(t) ≥ t+l} at b = t+l. Sortedness is necessary (`drop_sortedness`). Even total `n` is not even phase count (`drop_phase_count_for_total`).
6. **`reflection_sorted_pair`.** Composition of (2) and (5) through an independently supplied **exact equality** `hcount` between the occurrence phase count and the sorted threshold count.
   * Assessment: correct. Exactness is essential: `drop_bridge_count_le`, `drop_bridge_count_ge` and `drop_bridge_total_count` each satisfy every other hypothesis and violate the conclusion.
   * The hypotheses are jointly satisfiable with a non-vacuous conclusion (`pos_bridge_upper`: both members at or above the threshold; `pos_bridge_lower`: both below).
   * `hcount` is the candidate's "sorting preserves every recorded occurrence count". It is a hypothesis, not a construction, and coverage.json says so.
7. **`even_card_erase_pair`** and 8. **`even_phase_after_pair_removal`.** Statement: removing two distinct members of s that agree on P preserves the parity of the phase count.
   * Assessment: correct. Agreement (`drop_pair_agreement`), membership (`drop_erase_member`; `drop_pair_present`, where one member is absent from s although agreement holds) and distinctness (`drop_erase_distinct`) are each necessary.
   * "Including absent pairs" in the docstring means *absent from the phase* (`pos_pair_absent_from_phase`), not absent from s. When both members are absent from s the conclusion is trivially true, but that case is not an instance (`note_both_absent_trivial`). See O4.
9. **`lower_pair_visits_axis`.** Pure order logic: lowerEntry ≤ upperEntry ≤ b ≤ upperExit, plus tail agreement ⇒ the lower member visits b.
   * Assessment: correct. Both the entry order and tail agreement are necessary (`drop_entry_order`, `drop_tail_agreement`). This matches "the lower entry is at most the upper entry". Entry/exit order and the existence of both axis vertices are outside Lean.
10. **`odd_core_from_previous_failure`.** omega.
    * Assessment: correct. The hypothesis `1 < k` is superfluous (`note_odd_core_without_hk`; O3). The bound is tight (`pos_odd_core_tight`).
11. **`first_threshold_core`.** Uses `Nat.find` on `1 ≤ k ∧ count k ≤ 2k`.
    * Assessment: correct. It is the candidate's "first k with #{…} ≤ 2k … at the preceding failed threshold at least 2k−1".
    * Boundaries: `r ≥ 1` is necessary (`drop_first_threshold_start`). The `k = 1` disjunct cannot be dropped (`drop_k_one_branch`). `pos_first_threshold_k_one` covers k = 1. `pos_first_threshold_k_three` with `note_threshold_k_three_forced` covers a forced k = 3 carrying the odd core 5 = 2·3−1.
    * Converting counts into the "top 2k−1 layers" core still needs sortedness and is outside Lean.
12. **`exists_record_outside_alignment`.** Pigeonhole.
    * Assessment: correct. The count 2k+1 versus 2k is sharp (`drop_surplus_to_2k`), the cap is necessary (`drop_alignment_cap`), and k = 0 works (`pos_record_outside_k_zero`). The bound "at most 2k identical alignments" and the 2k+1 distinct unblocked occurrences themselves are outside Lean.
13. **`odd_core_budget`.** Identity 2(k−1)p + 2p = 2kp for k ≥ 1.
    * Assessment: correct. It needs k ≥ 1 (`drop_budget_k`) and is degenerate at p = 0 (`pos_zero_period_budget`).
14. **`shifted_copy_fits`.** δ + jp < kp for δ < p, j < k.
    * Assessment: correct, and stronger than the candidate's "last start ≤ kp−1". Tight (`pos_shift_tight`); k = 1 (`pos_shift_k_one`); vacuous at p = 0 (`note_zero_period_shift_vacuous`). Both bounds are necessary (`drop_shift_offset`, `drop_shift_index`).
15. **`fixed_deficit_surplus`.** Even positive δ ⇒ 2k+1 ≤ δ(k+1).
    * Assessment: correct. It is the candidate's fixed-r case, "Δ(r) … at least 2; the original k+1 placements suffice". Parity and positivity are each necessary (`drop_deficit_even`, `drop_deficit_positive`). The nonfixed partner sum (k+1)+k is not formalized (O5; reviewer arithmetic in `note_nonfixed_partner_sum`).
16. **`final_length_bound`.** 2·output = U, U ≤ 2W, W ≤ 2·OPT ⇒ output ≤ 2·OPT.
    * Assessment: correct, and it matches §7's U/2 ≤ W ≤ 2·OPT_RC. Each premise is necessary (`drop_half`, `drop_connection`, `drop_lower_bound`); the empty input is `pos_final_empty`.
    * This is scalar bookkeeping only. The half-Euler lemma, the connection cost and the count lemma are all hypotheses, so it gives **no** evidence for the target beyond confirming that the factors compose.

**Does any hypothesis encode the target?** No. No statement mentions words, reverse complements, OPT_RC, superstrings, graphs or algorithms. Every hypothesis is a local finite interface: an involution on codes, a phase predicate, an antitone exit sequence, an exact count equality, cardinal bounds, or scalar inequalities. The conclusions are parity, pair agreement, existence of a threshold, existence of an outside record, and scalar bounds. They are not restatements of the hypotheses. Positive controls show the hypothesis sets of 1, 2, 6, 8, 11, 12, 14, 15 and 16 are satisfiable, so none of them is vacuous.

**Depth.** The support is genuine but shallow:

* Substantive content: (1) the involution pairing; (3)–(4) the even-tail argument for downward-closed sets; (11) the minimal threshold; (8) parity under pair removal.
* Essentially one-line arithmetic: (9), (10), (12)–(16).
* All the hard mathematics is outside Lean: constructing the reflection on actual occurrences, proving that sorting preserves the count, the axis geometry, domination, hosting, quotient cycles, half-Euler, and complexity.

## Frozen `Controls.lean` assessment

All 7 compile with standard or no axioms, but none is stated against a frozen theorem. Each is a concrete numeral or Finset fact whose relevance depends on its docstring.

* `even_total_does_not_pair_threshold` (`Even 2 ∧ 2 ≤ 2 ∧ ¬2 ≤ 1`) is plain arithmetic. It becomes a counterexample only under the unstated reading n = 2, z = (2, 1), b = 2.
* `unordered_even_set_splits_pair`, `odd_tail_splits_pair`, `fixed_point_has_odd_card` and `no_outside_at_equal_cap` are informal witnesses. They omit the hypothesis structure, for example the filter of `range n` by P, or closure.
* `positive_odd_deficit_fails` and `unhalved_cost_can_exceed_factor_two` are adequate concrete instances.
* Absent entirely: phase preservation, closure/involution, exact count equality, sortedness in the z form, and pair membership or agreement.

The reviewer controls (`checks/ReviewerControls.lean`, 59 declarations) state each sensitivity test as the formal negation of the frozen statement with one hypothesis dropped or weakened. They supersede the frozen controls as sensitivity evidence (O1).

## Comparison to claimed coverage (coverage.json)

* **§1 (`shifted_copy_fits`, `fixed_deficit_surplus`):** accurate. External obligations listed. The unblocked-case and nonfixed-partner sums are not formalized and not claimed (O5).
* **§2 (9 theorems):** accurate. The listed external obligations (fixed-point-free involution on phase-labelled occurrences, phase preservation, exact count preservation under sorting, antitone exits, entry order, both axes) are exactly the hypotheses I found. The link from removal to re-pairing on the reduced list (re-indexing) is not formalized (O6).
* **§5 (4 theorems):** accurate. The conversion from cardinality to bands, records and geometry is listed as external, and k = 1 geometry is stated to be outside Lean.
* **§7 (`final_length_bound`):** accurate and explicitly conditional.
* The `not_formalized` list and `full_theorem_formalized: false` are accurate. The `control_theorems` are overstated as "hypothesis-sensitivity controls" (O1).

## Findings

**Required:** none.

**Optional:**

* **O1 (controls citation).** The frozen `Controls.lean` should not be cited as formal hypothesis-sensitivity evidence (see the assessment above). Cite the reviewer controls instead, or restate the frozen controls as negations of the frozen statements in any later version.
* **O2 (harness limits; no effect on this packet).**
  * `rebuild.py` does not compare printed types to expected statements; a weakened statement builds (M7).
  * Its declaration regex audits only `def`/`theorem`, not `lemma`/`instance`/`example`/`abbrev`.
  * Its forbidden-token regex misses `private axiom`, `implemented_by`, `extern`, `set_option` (for example `debug.skipKernelTC`) and notation or macro redefinitions. `private axiom` is caught later by `#print axioms` only when a listed declaration uses it (M5c).
  * It applies no resource limits, performs no kernel replay, and runs `git status` without `GIT_OPTIONAL_LOCKS=0`.
  * For this packet the gaps are closed by the human source reading (none of these constructs is present), the manifest hashes, and the reviewer's module-only leanchecker replay.
* **O3.** `odd_core_from_previous_failure` has the superfluous hypothesis `1 < k`. Harmless.
* **O4.** The docstring phrase "including absent pairs" should read "including pairs absent from the phase". Both members must lie in s, and one absent member breaks the statement.
* **O5.** The §1 arithmetic for the unblocked case and the nonfixed partner (`(k+1)+k ≥ 2k+1`) is not formalized. coverage.json does not claim it.
* **O6.** The composition "remove a full pair, re-index the remaining sorted layers, re-pair" is not formalized. Only parity preservation on an occurrence Finset is. Because pairs are removed whole from the top-aligned pairing, re-indexing preserves pair boundaries mathematically; this is reviewer reasoning, not Lean.
* **O7 (depth).** Most theorems are one-step arithmetic (see Depth). This is reading context for the size of the support, not a defect.

## Reading and trust limits

* Pinned upstream source truths at `fd4aeeb2…` are stipulated and were not audited. I did not read the upstream manuscript; the candidate's descriptions of source operations were used only to map statements.
* No proof-review verdict on candidate.md is given or presumed. Whether the external obligations hold (the reflection construction, sorting preservation, geometry, domination, hosting, cycles, half-Euler, complexity) is entirely outside this review. Nothing here asserts that the finite sets are the algorithm's actual occurrence sets.
* The trust base is the Lean 4.34.1 binary (hash recorded), the pinned dependency `.olean` files (read-only, not replayed), and the module-only leanchecker replay. No `--fresh` replay was run.
* The r1 artifacts were not relied on. Several r1 control ideas were reused after re-checking; provenance is in the header of `ReviewerControls.lean` and the docstring of `scripts/review_build.py`.
* Development failures are retained: `checks/dev/reviewer-build-try1` (a reviewer draft that failed on unnecessary `simp` calls, later removed) and `checks/attempt1-rlimit-as`.
* `scripts/mutation_tests.py` gained M5b, M5c and `--only` after the M0–M8 run. Cases M0–M8 are unchanged in the script. The source hashes after mutation are recorded in each `summary.json`.
* No contribution, priority, literature or acceptance verdict is made.

## Seal

`manifest.json` lists every file (bytes and SHA256) and every directory in this review packet except itself. `verify.py --anchor <SHA256 of manifest.json>`:

* checks the anchor format and hashes the raw manifest bytes **before** parsing;
* rejects a symlinked root or ancestor, symlinks, nonregular files, hard links, and extra or missing files or directories.

Seal controls (positive, wrong anchor, and tampering of copied packets) are recorded in `checks/seal-controls.log`. They were run against an interim manifest. The final manifest additionally contains that log, and the final anchor is reported in the handoff, not in this file.
