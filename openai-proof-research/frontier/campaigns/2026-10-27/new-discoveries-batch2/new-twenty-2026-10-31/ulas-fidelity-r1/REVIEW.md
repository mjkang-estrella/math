# Independent formal-fidelity review: MathDB 342364

This is a review, not acceptance. Root decides. No credit is claimed.

Reviewed packet: `../ulas-assembly-r1/ulas-source.zip`, SHA-256
`bafc3b63f6baba271680f2eed29334603149cee7c17a714bb7b4b1a04c37d3a1`.
All source references below are to the unchanged lane-local `extracted/src/` copy,
unless a different path is given. Line numbers count LF newlines, as `nl -ba` does.
The brief was read in full first, followed by the three required AGENTS files.

| Gate | Verdict |
|---|---|
| A. Definition fidelity | PASS |
| B. Proof structure | PASS |
| C. Independent semantic sanity | PASS |
| D. Bounded formal spot check | PASS |
| E. Manuscript readiness | QUALIFIED_PASS |

No formal source repair was identified. The qualifications concern manuscript
wording, prior-art access limits, and root's acceptance requirements, not an
unproved premise in these endpoints. This review does not establish novelty,
substantive credit, or completion of root's decisive replay.

## A. Definition fidelity

Primary source: `../expanded-corpus-r130/sources/1904.03398v1.txt`, lines
125–151 (generating product, colours, coefficient notation), 183–187 (C and its
power), and 1729–1735 (Conjecture 6.1). The raw MathDB record is
`../expanded-corpus-r130/raw/342364.jsonl:1`. Its three formulas and quantifier
ranges agree with the source. The generic phrase “m-colored binary partition”
must always be accompanied by the source's convention.

* `UlasSeries.lean:7–10`: `geomStep k` has coefficient 1 exactly when k divides
  the index. For the positive sizes used here it is the geometric series
  `(1-x^k)^(-1)`. `G N` has the extra `geomStep 1` and the factors with sizes
  `2^i`, i < N. Thus size 1 occurs twice. Raising to the m-th power gives 2m
  colours for size 1 and m colours for sizes 2, 4, 8, … . This matches source
  lines 139–141 specialized to binary partitions.
* `UlasSeries.lean:11–50`: coefficient agreement is preserved by multiplication
  and arbitrary natural powers; `G_agree` and `coeff_G_stable` prove eventual
  stability. The conservative cutoff N ≥ n+1 is sufficient because later sizes
  exceed n; no convergence or analytic assumption is used.
* `UlasSeries.lean:53–62`: C is the coefficientwise stabilized product, and
  `c m n` is literally `PowerSeries.coeff n (C^m)`. `C_agree` and `c_eq_finite`
  link this to finite products for every m and n. This is not a separate
  recurrence or a surrogate coefficient function.
* `UlasFinal.lean:5–7`: `diff m n = c m (4*n)-c m n`, `val m n` is
  `padicValInt 2` of that integer, and `targetEven` is the intended natural
  valuation expression. `EvenFormula`, `OddOneBound`, `OddThreeBound`, and
  `FifteenBound` explicitly include nonzero differences (lines 9–14, 38–39).
  The nonzero facts are proved, not assumed: `UlasPositive.lean:75–96` proves
  strict increase, positivity of the difference, and its nonvanishing for m,n ≥ 1.
  Thus `padicValInt 2 0 = 0` cannot create a false readout.
* `UlasFinal.lean:15–27`: both equality sets require positive n. `Conj61` (P1)
  has even k ≥ 1, all odd k ≥ 0, all n ≥ 1, and infinitude for each eligible k.
  `Conj61Some` (P2) retains every universal formula and changes only the three
  infinitude clauses to existence of an eligible k. Removing n = 0 from the
  source's final clause does not change infinitude. The source is phrased
  ambiguously enough that both readings must be named; neither endpoint claims
  P2 is false.
* `UlasFinal.lean:30–39`: `OddOneEquality` covers all positive odd n.
  `OddThreeEquality` covers positive odd n for m = 3 or 7 modulo 16 and n = 2
  modulo 4 for m = 11 modulo 16. `FifteenBound` covers every m = 16t+15 and
  every positive n, with the stronger constant 7. `NeverFifteen` (lines 45–46)
  excludes equality at constant 6 universally. These are the requested formulas.

The equality families are sufficient, not iff descriptions. In particular the
packet does not claim that equality for m = 3 occurs only at odd n. Each family
is genuinely infinite: n = a+1 in the even case; n = 2a+1 for each odd-index
family; and n = 4a+2 for the m = 11 modulo 16 family. For fixed a these satisfy
the required residues, and their values are unbounded as a increases.
`UlasFinal.lean:69–81` uses `Set.infinite_of_forall_exists_gt` with k = 1, 0, 0
and actual witnesses above each bound. The refutation at lines 62–66 selects
k = 3 in the last universal infinitude clause, obtains a positive member, and
contradicts `NeverFifteen` at t = 0. There is no vacuous quantified domain.

## B. Proof structure

`UlasFinal5.lean:6–15` contains precisely the three advertised unconditional
endpoints. All apply frozen `Ulas.full_theorem`, `Ulas.mathdb_342364`, or
`Ulas.conj61_some` to the same fully proved pair:
`⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩`.
The older conditional theorems are not treated as axioms.

The dependency spine is as follows; the retained declaration index and import
graph give exact locations of all remaining helper declarations.

1. The actual series transfer is proved in `UlasOperator.lean:44–52,110–129`
   and `UlasFinal2.lean`. The polynomial/series bridge is constructed using
   parity pairs in `UlasBridge.lean:29–101,136–192`. The explicit binomial
   operator is identified with this actual transfer in
   `UlasBinomial.lean:95–131`, especially the proved `binomialIdentification`
   and `lemma_R_unconditional`. Thus the formerly missing bridge Prop is
   discharged. `UlasReadout.lean:9–42` iterates the actual identity and obtains
   divisibility of the actual differences.
2. `UlasWeight.lean:9–10,73–174,181–241` defines a divisibility form of the
   bit-length weight (`Nat.size`, including size 0 = 0), proves the monomial
   gains, Lemma W and its tail strengthening, and the exact constant/main/tail
   formulas. `UlasExactReadout.lean:11–77` uses parity of C^m and divisibility
   at adjacent powers of 2 to prove exact valuations. Its hypotheses are
   supplied by the initializations and invariants below.
3. Even branch: `UlasEven5Pell.lean:25–79` proves the Pell factorization and
   actual initial representative `rho + reduced rho`. Coefficients and the
   binomial identity are proved in `UlasEven5Coefficients.lean:7–48`.
   `UlasEven5Kummer.lean:7–53` derives the central-binomial valuation from the
   mathlib digit formula and proves a sufficient coefficient bound, including
   vanishing outside the support. `UlasEven5Invariant.lean:8–87` proves the
   weighted and exceptional-index bounds, exact constant valuation, and
   `evenInitialization_proved`; `evenFormula_proved` invokes frozen
   `evenFormula_of_initialization`. In `UlasInvariant.lean:45–143` the invariant
   is preserved and iterated, and every positive n is factored into a power of
   2 times an odd number for the exact readout. No even initialization remains
   as an endpoint premise.
4. Odd branch: `UlasOdd5HalfAngle.lean:7–71`,
   `UlasOdd5Transfer.lean:7–45`, `UlasOdd5Crude.lean:7–73`,
   `UlasOdd5Factorization.lean`, and `UlasOdd5Representative.lean:7–76` prove
   the half-angle representation, actual transfer rules, square factorization,
   initial representative and coefficient bound `2^(2F+3)` for every odd m.
   `UlasOdd5One.lean:13–52` supplies the +3 bound and its odd-n equality.
   `UlasOdd5Coefficients.lean` establishes actual low coefficients of C;
   `UlasOdd5PowerCoefficients.lean:7–103` proves the coefficient polynomials of
   C^m through degree 12 by multiplication induction. Then
   `UlasOdd5LowIdentification.lean:24–85` identifies the first two reduced
   coefficients by actual differences at n = 2 and 3. The integer polynomial
   witnesses in `UlasOdd5Residues.lean:8–68` supply their required residue
   divisibilities and nondivisibilities. These are symbolic universal proofs,
   not an interpolation oracle or a finite check substituted for all m.
5. `UlasOdd5Bounds.lean:88–147` discharges `OddThreeBound` and `FifteenBound`
   through weighted actual readout and positivity.
   `UlasOdd5Equality.lean:14–91` supplies both +6 equality families using the
   initial constant or the constant after one reduced step.
   `UlasOdd5Final.lean:4–6` packages all five odd Props without hypotheses.
6. Frozen `UlasFinal.lean:48–81` derives `NeverFifteen`, packages the full
   theorem, refutes P1 and proves P2. `Remaining` is a definition of the six
   obligations, not an axiom, and the assembly supplies its inhabitant.

All three final types are closed, with no mathematical parameters or residual
Prop premises. The independent axiom output confirms only the three permitted
axioms transitively. No negative control or audit module enters their local
mathematical import closure.

## C. Independent semantic sanity

My `scripts/independent.py` multiplies one geometric series per colour for
sizes 1, 2, 4, … directly from the product, using exact Python integers. It does
not execute or import an inherited regression script, operator recurrence, or
Lean result. It ran with `python3 -I` under the caps. It checks m in
{1,2,3,4,5,6,7,8,9,11,15,19,23,27,31}, 1 ≤ n ≤ 64, computing through index 256:
960 pairs, zero failures. Every even formula, odd lower bound, stated equality
family, nonzero difference, and the +7/non-attainment assertion for m = 15,31
passed. Numerical testing is corroboration, not proof of the universal claims.

My `scripts/ReviewExamples.lean` was strictly compiled against the new extracted
build. It proves c_15(1) = 30, c_15(4) = 48030, c_31(4) = 738110; ten separate
n = 1 differences and exact valuations via the low coefficient polynomial and
adjacent divisibilities; and four direct checks using the power coefficients at
indices 8 and 12. These direct coefficient proofs do not invoke the endpoints.
It also specializes the full endpoint at even m, all three odd equality residue
families, and both never-equality colours. Both initial and extended example
runs passed. All values agree with the independently computed product.

| m | n | c_m(n) | c_m(4n) | difference | valuation |
|---|---|---|---|---|---|
| 15 | 1 | 30 | 48030 | 48000 | 7 |
| 4 | 2 | 40 | 19304 | 19264 | 6 |
| 11 | 2 | 264 | 8627080 | 8626816 | 7 |
| 3 | 3 | 74 | 42634 | 42560 | 6 |
| 31 | 2 | 1984 | 11824515008 | 11824513024 | 14 |

## D. Bounded formal spot check

A safe fresh extraction from the specified source-only zip was built entirely
in this lane. All 43 src modules, hence the whole endpoint import closure of
local source modules and extra supplied audit modules, passed the pinned Lean
4.34.1 compiler with `-j1 -M3500 -DwarningAsError=true`. The read-only upstream
package path is the one supplied by the brief, with the stipulated mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`. I did not run git to revalidate that
upstream revision or audit upstream mathematical truth.

The independent `leanchecker UlasFinal5` run exited 0. The endpoint build and
both example runs printed these exact transitive axiom sets:

* Ulas.Final5.full_theorem_E2: propext, Classical.choice, Quot.sound.
* Ulas.Final5.mathdb_342364: propext, Classical.choice, Quot.sound.
* Ulas.Final5.conj61_some: propext, Classical.choice, Quot.sound.

My lexical scan `scripts/scan.py` strips nested block comments, line comments,
and quoted strings before looking for sorry, admit, axiom, unsafe, partial,
native_decide, ofReduceBool, implemented_by and extern. It scanned all 55
archived Lean files (43 src, 11 controls, one audit script): zero findings.
The 54 mathematical/control source hashes match the assembly results manifest;
every extracted archive file remains byte-identical to its zip entry.

The assembly's much larger declaration audit is documented in its hash-bound
results and summaries. I did not independently rerun its eight audit shards,
its 43 leanchecker calls, or its 11 negative controls. This bounded review does
not claim root's decisive full replay. Root must still perform that replay and
any required closure metadata audit/controls before acceptance.

Every heavy call was serial, with affinity CPUs 0,1, CPU limit 120 seconds,
wall timeout 140 seconds, MALLOC_ARENA_MAX=2, and the supplied RSS monitor at
6 GiB. Peak reported build RSS was 2,765,992 KiB. TMPDIR and XDG_CACHE_HOME
point inside this lane; all build outputs are lane-local. Full stdout, stderr,
resource measurements and exit receipts are retained per call. No job remains.

## E. Manuscript readiness and required fixes

The formal certificate is suitable for root's next review stage. The manuscript
must be brought into correspondence with the final symbolic proof. No new
manuscript was written or accepted in this lane. The reviewed r130 draft and
prior review identify the following necessary manuscript work:

1. State the entire seven-part conjunction from `UlasFinal5.lean:6–9`, including
   every k/n range, both odd bounds, the sufficient equality families, the
   universal +7 bound, and never equality for all m = 15 modulo 16. Explain
   P1 versus P2 and derive both respective endpoints. The example 48000 alone
   is not the resolution being offered for credit.
2. Define C, c, the extra unit factor/colour convention, diff and valuation;
   explain finite-truncation stability and the nonzero differences. Cite the
   literal source and MathDB statement. Include the statement correspondence.
3. Present the Chebyshev/Pell section operator, its preservation of integral
   polynomials, Lemma R with the actual-series bridge, and Lemma W with the
   bit-length zero convention and exceptional main terms. State the even
   initialization, its invariant and Kummer estimate, the odd half-angle
   initialization, crude bound, exact readout and low coefficients.
4. Repair the draft's inconsistent interpolation degree discussion and the
   mismatch between claimed >=11 and a certificate only checking >=8.
   Prefer the final Lean route: multiplication induction through index 12,
   reduced low-coefficient identities, and explicit symbolic residue witnesses
   proving >=11. The final formal proof needs no interpolation certificate.
5. Say “sufficient infinite equality families”, never “exact equality sets”
   as an iff classification. The m = 15 modulo 16 never statement is universal.
   Root's older adjudication uses “exact equality sets”; root must reconcile
   that wording with the expressly reviewed sufficient-family result before
   acceptance. This review follows the present brief's explicit sufficiency
   requirement and does not silently strengthen the theorem.
6. Document the packet/toolchain hashes, strict builds, kernel checker,
   permitted axiom sets, forbidden-token and declaration metadata audits,
   negative controls, independent product checks, and root replay distinctly.
   Computational examples do not replace the formal universal proof.
7. Retain bounded prior-art/access caveats. This review made no network calls
   and supplies no new novelty clearance. The earlier review did not obtain
   the Żmija 2023 body, encountered a USM thesis 403, did not check the full
   Google Scholar graph, and excluded Crossref/Semantic Scholar/arXiv API
   searches in that review. Do not upgrade those limits into exhaustive
   absence-of-prior-proof claims. Root must perform its current checks under
   campaign rules before acceptance. No publication/upload is authorized here.

Required formal source fixes: none found. Required manuscript fixes: items 1–7.
Required acceptance work: root's decisive replay and adjudication, including
resolution of the historical “exact” wording and novelty/access qualifications.

## Evidence and integrity

`input-hashes-before.json` and `input-hashes-after.json` contain the complete
SHA-256 map for all 17 required read-only inputs. They are identical. They cover
the archive, four assembly documents, six round summaries, both prior review
files, r130 proof/raw/source, and root adjudication. The independently checked
archive hash is the exact hash in the brief.

`extracted/logs/build-*.log`, `.stderr`, `.result.json` retain all 43 strict
builds. `logs/examples-*.{log,stderr,result.json}` and
`logs/examples-extended-*.{log,stderr,result.json}` retain both example runs;
`logs/independent-*` retains the full exact product output;
`logs/checker-*` retains the endpoint checker run. `logs/source-scan.json`,
`logs/declaration-index.json`, `logs/import-graph.json` and
`logs/verification-summary.json` provide the scan, navigation and build/hash
summary. The replay and bounding scripts are in `extracted/scripts/`; my scripts
are in `scripts/`. A manifest of scripts and logs is `evidence-hashes.json`.

No child agents, git, shared ledger edits, network calls, external messages,
browser tabs, publication or uploads were used. All writes stayed in this
review lane. No self-acceptance or campaign-count change is made.
