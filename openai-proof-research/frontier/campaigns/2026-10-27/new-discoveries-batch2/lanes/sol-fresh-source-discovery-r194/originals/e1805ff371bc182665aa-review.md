# T205M independent scoped formal-support review, round 1

Reviewer: Claude Opus 5.5 (Factory Droid), acting as the assigned review sub-agent.
Original reviewer prose CC BY 4.0; reviewer code MIT. Date: 2026-10-18.

## Verdict

**PASS_SCOPED_T205M.** No required repairs.

This verdict covers only the frozen finite-poset support packet
`t205m-formal-v1` (external manifest SHA256
`3037eddfa1f64be85b646090df0f49484b84ff625eb0970074af86c3948ce2f2`).
It is not a verdict on the full T205M theorem, its contribution, novelty,
acceptance or the campaign count. The full proof gate (PASS_FULL_T205M at
`t205m-proof-r1`, external `4b41e5dd…4343`) and the contribution gate
(SUBSTANTIAL, narrowly, with the mandatory copied credit addendum) are
separate records that this review did not re-adjudicate. Count 14/20 is
unchanged by this review. Hashes and builds establish identities and kernel
acceptance, not mathematical truth of the source inputs or the full theorem.

## 1. Identity work, done before trusting the inventory

* SHA256 of `t205m-formal-v1/manifest.json` equals the dispatch anchor
  `3037eddf…ce2f2`. A reviewer-written walk (not the packet's `verify.py`)
  reproduced the exact inventory: 20 regular single-link files, directories
  `inputs` and `validation`, no symlinks. The packet `verify.py` was read
  and then run: positive anchor PASS, all-zero anchor rejected with
  `external anchor mismatch`.
* Copied inputs are byte-identical to their originals and to the dispatch
  anchors: author manifest `29ab2fdb…1db9` (equal to the SHA256 of
  `fresh-arithmetic-discovery-r38/manifest.json`), candidate `17b2b35c…20c5`,
  parent high-capacity proof `fc155c9a…6430`, scope `3eb9d790…64f6`, credit
  addendum `c8c13a93…b616`.
* `T205M.lean`, `Controls.lean`, `rebuild.py`, lockfile, toolchain,
  lakefile and the validation records are byte-identical to
  `t205m-formal-development-r1`. Its README and provenance hashes equal those
  recorded in `provenance.json`. `rebuild.py` differs from the T027O builder
  (`bdd5e4b7…07e2`) only in three module-name lines. The lockfile equals the
  T027O lockfile (`9dc9e019…e233`). The packet is committed (`7e2f520c`) and
  `git status` is clean for it before and after this review.
* After all builds and controls the packet was re-authenticated with the same
  anchor and exact inventory, and `git status` remained clean.

## 2. Scripts read before running

All packet scripts were read in full before execution: `verify.py`
(read-only inventory check), `integrity_controls.py` (copies the packet into a
`/var/tmp` temporary directory per case) and `rebuild.py`. The builder:

* checks each of the nine lockfile revisions with `git rev-parse HEAD`,
  tracked-file cleanliness with `git status --porcelain --untracked-files=no`,
  and mathlib `d13f23b7…1612`;
* checks the Lean binary reports 4.34.1 and commit
  `5045d0056413266e57c625dcd7c365b10e377c52`;
* rejects `sorry|admit|unsafe|native_decide` and line-initial `axiom`;
* compiles the two sources with `lean -o` in a fresh temporary directory
  inside the new output directory, using the cached dependency `.olean`
  libraries on `LEAN_PATH`;
* fails on any `error:` or `warning:`, then prints `#check @` and
  `#print axioms` for every regex-matched `def`/`theorem` and allows only
  `propext`, `Classical.choice`, `Quot.sound`.

It never invokes `lake` or the network and never writes to the cache, apart
from the possibility, noted below, that `git status` refreshes an index.

## 3. Fresh build outside the packet

Recorded in `execution.json`, `builder-run/` and `independent-logs/`.
`run_review.py` was written by the reviewer; it is the driver for all
execution steps.

* The packet builder ran with its **defaults** (no `--cache`/`--lean`
  override) as `rebuild.py --output /var/tmp/t205m-formal-review-r1-dwsl7i5c/builder-output`.
  The default cache resolves to `frontier/campaigns/2026-10-14/formal/.lake/packages`,
  the shared cache. The Lean binary SHA256 was `e8baaa71…5550`. All nine pins
  matched the lockfile, and the tracked trees were clean. Result:
  `PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS`, with 7 support and
  10 control declarations. The fresh `receipt.json` is byte-identical to the
  frozen `validation/receipt.json` (`52442cd3…17e2`). The fresh `Checks.lean`,
  `types-axioms.log`, and the empty `support.log` and `controls.log` are
  byte-identical to the frozen copies.
* I read every printed type and axiom list. All 17 audited declarations
  depend only on standard axioms. `antichain_noncomparable` depends on none,
  and `chainPrefix` depends only on `propext` and `Quot.sound`.
* Dependency cache: the driver fingerprinted 148,428 cache entries (path,
  mode, size, mtime, ctime) before and after the complete run, including all
  mutation controls. The two fingerprints are identical (`ddecc55a…cb22`).
  `GIT_OPTIONAL_LOCKS=0` was set for every git call, so `git status` could not
  refresh dependency indexes.
* **Trusted-cache limit.** The pinned dependency `.olean` objects were
  neither rebuilt nor hashed against their sources. Git pins and
  tracked-source cleanliness do not certify untracked build products.
  Kernel acceptance is relative to those trusted objects and to the Lean
  4.34.1 kernel.

The reviewer's own scan of `T205M.lean` and `Controls.lean` found no
`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`,
`extern`, `opaque`, `set_option`, `macro`, `elab` or `attribute`.

## 4. Independent Lean checks (`Independent.lean`)

The driver compiled fresh copies of the two author sources and then the
reviewer file, all under `/var/tmp`. There were no errors and no warnings.
All 23 reviewer constants use only standard axioms.

**Statement pins.** Each `example` restates an author type in the reviewer's
own wording and is closed by the author term:

* `IsIdeal s ↔ ∀ x y, y ∈ s → x ≤ y → x ∈ s`;
* interval rank;
* unique-rank cross-comparability as `∀ a ∈ s, ∀ b ∉ s, a ≤ b`;
* the second-ideal theorem;
* the two-ideal criterion.

**Semantics of `IsIdeal`.** `isIdeal_iff_isLowerSet` proves equivalence with
Mathlib's `IsLowerSet` on the coerced set. This makes `IsIdeal` genuine
downward closure in an arbitrary partial order, with no decidability
argument. `not_every_set_is_ideal` shows `{1} ⊆ Fin 2` is not an ideal, so the
predicate is not vacuous.

**Rank interpolation is proved, not assumed.** `ideal_insert_minimal` takes a
minimal element `x` of `t \ s` (via `Finset.exists_minimal`). If `a ≤ x`,
then `a ∈ t` because `t` is an ideal. If `a ∉ s`, minimality gives `x ≤ a`,
so `a = x`. Hence `insert x s` is an ideal inside `t`. `ideal_interval_rank`
iterates this by induction on `r − |s|`. Its hypotheses are ideals
`s ⊆ t` and `|s| ≤ r ≤ |t|`; the conclusion makes no assumption about rank.
Necessity controls written by the reviewer:

* `interval_lower_bound_needed`: with `s = t = univ (Fin 2)` and `r = 0`, no
  ideal exists;
* `interval_upper_ideal_needed`: with `t = {1}` in the chain `Fin 2` and
  `r = 1`, no ideal exists.

The author's `rank_upper_bound_cannot_be_dropped` covers `r > |t|`.

**Uniqueness yields inside ≤ outside by principal-ideal interpolation.** Let
`d = {x | x ≤ b}` be the principal ideal of the outside element `b`.

* If `|d| ≤ |s|`, extend `d` inside `univ` to rank `|s|`. Uniqueness forces
  the extension to equal `s`, which then contains `b`, a contradiction.
* Otherwise, truncate inside `d` (starting from `∅`) to rank `|s|`.
  Uniqueness forces `s ⊆ d`, so `a ≤ b`.

Uniqueness is quantified over all ideals of the full finite ambient type. No
linear extension and no comparability are assumed. The parent's
linear-extension argument is replaced by this route, with the same
conclusion.

* `_hs` is redundant, as the dispatch states. `ideal_of_unique` proves
  `IsIdeal s` from uniqueness alone, via an ideal of rank `|s|` from
  `∅ ⊆ univ`. `cross_comparable_without_hs` then removes `_hs`. Keeping
  `_hs` in the API is harmless and is not a gap.
* Converse: `unique_of_cut` proves that an ordered cut is the unique ideal of
  its size. Uniqueness at a cardinality is therefore *equivalent* to the
  ordered-cut property. The hypothesis is exact, neither weaker nor stronger
  than needed.

**Second ideal and the two-ideal criterion.**

* `exists_second_ideal_of_incomparable` is the contrapositive.
* `two_ideals_of_no_cut` obtains some ideal of rank `r ≤ |α|` from
  `∅ ⊆ univ`, extracts an incomparable inside/outside pair from `hno`, and
  produces a second ideal.
* `two_ideals_iff_no_cut` (reviewer) proves that, at feasible ranks, `hno`
  is necessary as well as sufficient.

Consequently the formal theorem is a lossless *reduction*. It replaces
"at least two ideals of rank r" with the per-ideal condition "no rank-r
ideal is an ordered cut". It does not discharge that condition. The
conclusion is not hidden in an assumption in the sense of restating it. The
hypothesis is logically equivalent, by design, and the entire geometric
difficulty lies in proving `hno`. That step is **unformalized** (§5).

Reviewer controls:

* `antichain_two_ideals` instantiates `two_ideals_of_no_cut` nonvacuously.
  No author control exercises that theorem.
* `no_cut_hypothesis_needed`: in the chain `Fin 4` at rank 2, two ideals do
  not exist.
* `two_ideal_rank_bound_needed`: at `r = 3 > |Two|`, `hno` holds vacuously
  but the conclusion fails.

**Hidden-assumption mutation control.** A `/var/tmp` copy added the
conclusion `∃ s t, …` as an extra hypothesis `_h2` of
`two_ideals_of_no_cut`. The packet builder *accepted* the mutant,
`PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS`, because a valid theorem
with a stronger hypothesis passes every build and axiom check. The reviewer
statement pins *rejected* it: the author modules compiled, and
`Independent.lean` failed with an error. Build and axiom audits therefore
cannot replace the semantic reading in this section.

**Applications and controls in `Controls.lean`.**

* Chain `Fin 4`. `chainPrefix = {0,1}` is an ideal, and
  `chainPrefix_unique` is checked by kernel `decide` over all 16 subsets.
  `chainPrefix_cross` is a nonvacuous instance of unique-rank
  cross-comparability.
* Product `Fin 3 × Fin 3`. Mathlib's `Prod` order is componentwise; the
  reviewer pinned `Prod.le_def` for `ℕ × ℕ` and the subtype order as the
  restricted order. `product_has_rank_four` only exercises the existence of
  an ideal from `∅` to `univ`. It does not test cut/uniqueness on a
  two-dimensional poset.
* Antichain `Two` (`le := Eq`). `antichain_second_ideal` applies the
  second-ideal theorem. `uniqueness_cannot_be_dropped` correctly shows that
  cross-comparability fails for the ideal `{left}` without uniqueness.
* `rank_upper_bound_cannot_be_dropped` correctly shows that no 4-element
  ideal exists in `Fin 3`.

All controls are genuine kernel-checked examples. None is numerical evidence
for T205M.

**Precise coverage, verified by enumerating the environment.**

* The builder's 17 audited names are: `T205M.lean`, 1 definition
  (`IsIdeal`) and 6 theorems; `Controls.lean`, 1 definition (`chainPrefix`)
  and 9 theorems.
* The `T205M` module contains 12 constants: those 7 plus 5 compiler
  `_proof_` auxiliaries.
* The `Controls` module contains 41 constants. They include the inductive
  `Two` and its constructors and recursors, the generated
  `T205M.IsIdeal.eq_1` and `chainPrefix.eq_1`, `_proof_` auxiliaries, and
  **five** instance constants:
  * the three explicit instances `instFintypeTwo`, `instPartialOrderTwo`
    and `instDecidableLETwo`;
  * the derived `instDecidableEqTwo` from `deriving DecidableEq`;
  * the automatic `Two._sizeOf_inst`.
* Every constant in both modules was checked with `collectAxioms`. All are
  standard, and none is an `axiom` declaration.
* "Two type + 3 instances" is accurate for the instances written explicitly.
  The derived `DecidableEq` instance, which the antichain theorems use, is
  an additional auxiliary instance that the README does not mention. It is
  audited directly here and indirectly through the theorems that depend on
  it. This is editorial only (E1).

## 5. Exact role in the parent skew-poset proof

The parent proof `parent-high-capacity.md` uses the following setup:

* `m ≥ 7`, `h = m − 2`, `S = λ/μ` with `μ = (λ₅, λ₆, …)`;
* the coordinate order on cells;
* ideal rank `k = C − (2m−1)`.

Here is what the formal packet supplies when instantiated at `α = S`, taken
as a subtype of `ℕ × ℕ` with the induced componentwise order.
`cells_ideal_every_size` and `cells_two_ideals_of_no_cut` show that this
instantiation typechecks for every finite cell set.

1. "Suppose A is the unique ideal of rank r. Every a ∈ A, b ∈ B satisfies
   a ≤ b." This is exactly `unique_rank_cross_comparable`, or the `_hs`-free
   form. **Formalized.**
2. "Every rank 2 ≤ r ≤ C−2 has at least two ideals" follows from
   `two_ideals_of_no_cut` *once* `hno` is proved for `S`. The reduction is
   **formalized**. The proof of `hno` is **unformalized**: the column extrema
   `c, d`, the bounds `H₁ ≤ L_w`, `L_j = max(1, H_j−3)`, the monotone column
   heights, and the use of `C ≥ 2m+1`.
3. "Every finite poset has an ideal of each size," used for `S′` in the
   exception case, is `ideal_interval_rank` from `∅` to `univ`.
   **Formalized** for an arbitrary finite poset.
4. The following are **UNFORMALIZED**:
   * the bijection between ideals of `S` and partitions `μ ⊆ ν ⊆ λ`;
   * the arithmetic `2 ≤ k ≤ C−2`;
   * the disjoint chain/`S′` decomposition and its incomparability;
   * the count `min(4,k)+1`;
   * the exceptional set `E_h`, its fit conditions and lengths, and the
     "at most two exceptions" argument;
   * the rank-two inequality `C ≥ 4(m−3) > 2m+1`.
5. Everything in the candidate outside §5's combinatorial core is also
   **UNFORMALIZED**:
   * partitions, skew geometry and the four-strip criterion (8);
   * the semistandard filling, LR/Pieri positivity and Kostka numbers;
   * the source cyclic module, band quotients and induced modules;
   * Saxl-type source contracts, representation theory and sign invariance;
   * the wide and low-capacity cases;
   * the finite bases at `m = 7, 8` and `h = 5, 6`;
   * the full strong induction and the corner-formula sharpness.

## 6. Integrity controls

**Packet controls.** The driver ran `integrity_controls.py --anchor 3037…`
on disposable `/var/tmp` copies. It first authenticated the original. All 15
cases matched their exact reasons: only `positive` was accepted, and the 14
negatives (wrong or malformed anchor, changed, missing or extra
file/directory, root/ancestor/payload symlinks, hardlinks, fifo, nested
manifest, self-reseal) were rejected. The output
(`packet-integrity-controls.json`) is byte-identical to the parent's
recorded `formal-v1-integrity-controls.json`.

**Reviewer mutation controls.** Each mutation ran on a `/var/tmp` copy of
the packet, and the original was re-authenticated after each case.

| Case | Checker | Outcome | Exact reason |
|---|---|---|---|
| `sorry` in a proof | builder | rejected | `forbidden proof escape: T205M.lean` |
| line-initial `axiom` | builder | rejected | `forbidden proof escape: T205M.lean` |
| `private axiom` used by a new theorem | builder | rejected | `unapproved axiom dependency: T205M.leak` (the regex misses it; the axiom audit catches it) |
| swapped arguments | builder | rejected | `compile failed or warned: support` |
| upward-closure definition | builder | rejected | `compile failed or warned: support` |
| mathlib lockfile pin | builder | rejected | `dependency pin mismatch: mathlib` |
| conclusion added as hypothesis | builder | **accepted** (expected) | `PASS_SCOPED_…` |
| conclusion added as hypothesis | reviewer pins | rejected | `Independent.lean:` error, with the author modules compiling |

**Review seal.** `seal.py` writes `review-manifest.json`, which lists
every other file and directory here with its size and SHA256. The manifest's
own SHA256 is the external anchor, reported outside this directory.
`verify.py --anchor HASH` checks that anchor, the verdict metadata and the
exact inventory, with no symlinks, hardlinks or non-regular files.

`review_controls.py --anchor HASH` first authenticates the original, then
runs 16 cases on `/var/tmp` copies:

* positive;
* wrong and malformed anchors;
* changed review prose or Lean, a missing log, an extra file, directory or
  nested manifest;
* payload, root and hardlink links, and a fifo;
* manifest hardlink, self-reseal and verdict edit.

The script was run after sealing. Its output is reported with the external
anchor, not stored here, because storing it would change the sealed
inventory.

## 7. Required repairs

None.

## 8. Optional editorial items (not required)

* **E1.** The coverage sentence could mention the derived `DecidableEq Two`
  instance and the automatic `SizeOf` instance in addition to the three
  explicit instances.
* **E2.** No author control instantiates `two_ideals_of_no_cut`.
  Optionally add a nonvacuous instance, such as the reviewer's
  `antichain_two_ideals`, and the necessity controls for `hno` and `hr`.
* **E3.** The builder's regex inventory captures only line-initial
  `def`/`theorem`, and its escape scan misses `private axiom`. Dependency
  axioms are still caught, as the mutation shows. An environment-based
  inventory, as in `Independent.lean`, would be more robust.
* **E4.** The builder could set `GIT_OPTIONAL_LOCKS=0` so that `git status`
  can never refresh a dependency index. This review set it. Default runs
  without it were not separately fingerprinted.
* **E5.** `lake-manifest.json` keeps the project name
  `t027o_scoped_support` while `lakefile.toml` says `t205m_scoped_support`.
  This is cosmetic, because the builder does not invoke `lake`.
* **E6.** The receipt's `network_used: false` and
  `dependency_cache_modified: false` are asserted constants, not
  measurements. This review measured the cache instead.
* **E7.** The README says that compilation logs "are retained under
  `validation/` after a successful build". The builder writes to its
  `--output` directory, and `validation/` holds the copied development
  records.

## 9. Full-theorem limits

The packet formalizes three facts about finite posets:

* rank interpolation of ideals;
* the equivalence-direction lemma "unique rank ⇒ ordered cut";
* the two-ideal reduction.

It formalizes no statement about partitions, skew diagrams, exceptional
shapes, Kostka or Littlewood–Richardson coefficients, symmetric-group
representations, tensor-square multiplicities, the cyclic source module, or
the induction proving `g(ρ_m, ρ_m, λ) ≥ m−1`. The geometric no-cut condition
for `λ/μ` remains a mathematical (proof-gate) obligation. A formalized
supporting lemma is not a formalized full theorem. Any manuscript coverage
statement must say exactly this.
