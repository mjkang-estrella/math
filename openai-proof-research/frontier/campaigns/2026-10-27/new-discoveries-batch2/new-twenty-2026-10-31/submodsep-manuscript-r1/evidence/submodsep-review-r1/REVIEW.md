# Independent adversarial review: MathDB 341850

**Recommendation: HOLD.** The claimed refutation and Lean endpoint are correct. Do not package for acceptance yet: the final 2022 journal statement has not been read, and a materially simpler application of a published 2021 obstruction must be considered in the campaign's routine-corollary screen. This is a review, not an acceptance or credit decision.

| Gate | Verdict | Finding |
|---|---|---|
| A: statement fidelity | QUALIFIED_PASS | Exact arXiv v1 and ECCC statements match MathDB; final journal body remains unverified. |
| B: independent mathematics | PASS | All 120 permutation expansions cancel exactly; upper bound is −840. All four small-case witnesses check exactly. |
| C: Lean fidelity and replay | PASS | Fresh strict rebuild, explicit-module kernel checker, independent metadata/axiom audit of 45 local declarations pass. |
| D: prior art | QUALIFIED_PASS | Bounded live screen found no published application to this monomial family, but a published dependency-cycle criterion already proves impossibility once a four-edge cycle is supplied. |
| E: significance/exclusions | QUALIFIED_PASS | Genuine interior-parameter counterexample to the literal conjecture; novelty of the obstruction method cannot be claimed. Routine-corollary eligibility needs explicit root adjudication. |

## A. Source and statement

The authors are **Joshua Brakensiek, Sivakanth Gopi, and Venkatesan Guruswami**. The preprint title is *CSPs with Global Modular Constraints: Algorithms and Hardness via Polynomial Representations*. The journal expands “CSPs” to “Constraint Satisfaction Problems” (SIAM Journal on Computing 51(3), 577–626, 2022, DOI 10.1137/19M1291054).

I fetched the live [arXiv listing](https://arxiv.org/abs/1902.04740), [ECCC listing](https://eccc.weizmann.ac.il/report/2019/013/) and [ECCC PDF](https://eccc.weizmann.ac.il/report/2019/013/download/). ArXiv lists only v1, submitted February 13, 2019 (`downloads/arxiv-abs/body:163–165`). ECCC lists TR19-013, January 31, 2019, and no revision (`downloads/eccc-page/body:168–200`). Both available paper bodies retain Conjecture 3.33. ECCC and arXiv are distinct files, not a journal-version equivalence certificate.

The following is a mathematical transcription of the PDF's surrounding text and conjecture, retaining the source's subset symbol and spelling. The raw extracted text, including line breaks, is also preserved in `source-quote-extracted.txt`; see `arxiv-v1.txt:1334–1351`, `eccc.txt:1337–1354`, and the inspected rendered PDF page `tmp/conjecture-25.png` (printed page 23):

> closely related to the existence of (M, r, d)-systems and so to HORN-SAT-MOD_M. We showed that, assuming ETH, HORN-SAT-MOD_M cannot solved in polynomial time if M is not a prime power. Can we show a similar hardness result for SUBMOD-MIN-MOD_M? The following conjecture will imply such a hardness result.
>
> Let 0 ≤ r ≤ d be integers and let n = binom(d, ≤r). Let φ : {0, 1}^d → {0, 1}^n given by φ(x) = (∏_{i∈S} x_i)_{S⊂[d]:|S|≤r}. Let F_{r,d} = φ({0, 1}^d). Note that if we think of F_{r,d} as a collection of subsets of [n], F_{r,d} is an intersection-closed family.
>
> Conjecture 3.33. For every 0 ≤ r ≤ d and n = binom(d, ≤r), there exists a submodular function f : {0, 1}^n → Z such that:
>
> 1. f(x) can be evaluated in poly(n) time for every x ∈ {0, 1}^n.
> 2. For all x ∈ F_{r,d} (defined as above), f(x) ≤ −1 and for all x ∉ F_{r,d}, f(x) ≥ 0.

The index includes the empty subset, whose monomial is 1. The displayed dimension counts all subsets of size at most r. The notation ⊂ is used for subset inclusion; interpreting it strictly when r=d would conflict with the displayed dimension. In our interior instance r=2<5 this notational issue cannot affect the result. There is no fixed-r/asymptotic-only qualification or restriction on moduli in the conjecture itself. The discussion of non-prime-power moduli motivates it; it does not restrict its quantifiers. The integer codomain and both weak sign inequalities agree with `../expanded-corpus-r198/raw/341850.json:1` and the ID-keyed results entry. The raw record's open label is historical metadata, not novelty evidence.

The source's Proposition 3.34 and Corollary 3.35 (`arxiv-v1.txt:1353–1379`) explicitly assume this conjecture for a proposed modular-submodular hardness reduction. The certificate refutes the conjecture; it proves neither tractability nor hardness of the modular optimization problem.

**Unclosed version check:** the discovery receipt records a 403/challenge at the SIAM PDF route. I did not retry that route or follow any redirect to its denied host. Fresh author publication pages link arXiv/ECCC; neither identifies an accepted manuscript with journal-equivalent text. The journal is a 50-page version of record, so unchanged numbering or wording must not be inferred. Obtain the journal section or a demonstrably journal-equivalent accepted manuscript and inspect the conjecture and any correction/withdrawal before acceptance. No later arXiv/ECCC withdrawal was observed; a journal withdrawal remains unchecked.

## B. Independent exact verification

I wrote `scripts/mathcheck.py`; it neither imports nor runs discovery code and ignores the supplied orbit and representative arrays. It independently builds the five singletons followed by ten lexicographic pairs, the 32 good masks, and all 120 permutations. The constant coordinate is fixed to 1. This is a lattice face: meet and join are bitwise AND and OR, with the constant still present. Intersecting the full monomial image with this face gives exactly these good masks.

For each of the nine submodular rows, the script checks the four coefficients, positive integral weight, original meet/join identities, and their images under every permutation. For each of the four sign rows it checks good/bad membership under each permutation. The expanded coefficient vector on actual masks, not just orbit labels, vanishes: **1,080 submodular row instances, 365 touched masks, zero residual coefficients**. Good rows have total weight 7, giving −120·7 = **−840**. Thus the hypothesized separator would imply 0 ≤ −840. See `logs/mathcheck-bound.log:1` and `math-receipt.json`.

Symmetrization is a finite sum g(P)=Σσ f(σP). Coordinate permutations preserve lattice operations, allowed coordinates, and the monomial image. Summing the submodular inequalities preserves submodularity; good values are at most −120, bad values at least 0; right multiplication permutes the group summation index, giving orbit invariance. No division, integrality gap, or computational assumption enters this argument.

The four feasible small cases are independently verified using supplied *data*, not discovery scripts. Decimal values are rationally reconstructed with denominator at most 10^6; every resulting sign and elementary submodularity inequality is then checked with exact Fraction arithmetic. Successful cases (d,r)=(2,2),(3,2),(3,3),(4,2) have respectively 6, 240, 672, and 11,520 elementary inequalities. These imply full submodularity by the standard telescoping diminishing-returns argument. To include the constant-coordinate-0 slice, extend a face witness h by h(m)+C(1−z), with C≥−min h. This is a modular addition to a submodular function and makes every constant-0 point nonnegative. Suitable C are 2, 4, 1283/177, 10. Clearing denominators yields integer-valued full-cube witnesses. These checks establish feasibility, not minimality over every other parameter.

Initial unsuccessful checks are retained: `logs/mathcheck.log` records missing numpy; `logs/mathcheck-final.log` was overwritten during correction, so the exact-decimal assertion failure survives in the tool history rather than as a separate final file. The final successful independent run is `logs/mathcheck-bound.log`. No software was installed and no LP solver was needed.

## C. Formal fidelity and replay

I safely extracted the hash-matching packet into a fresh lane-local directory, rejecting absolute/traversal paths, symlinks and oversized entries (`scripts/prepare.py`). I read all 67 lines of `build/fresh/lean/Separator.lean` and all 146 lines of `Certificate.lean`, including each finite normalization permutation and row identity.

* `Separator.lean:7–14`: points are subsets of subset-labeled coordinates; allowed labels have cardinality ≤r. The allowed part is exactly the Boolean cube on n=Σ_{k≤r} binom(d,k) labels. The redundant values on disallowed points impose no additional restriction and can always be extended arbitrarily. `phi` contains precisely the labels whose monomials evaluate to 1, including ∅. The separator's submodularity is required on **every** allowed point, not only the image or the face. `SeparationExistence` has the literal universal d,r quantifiers and r≤d condition.
* `Separator.lean:16–66`: actual variable permutations, group summation, orbit invariance, preservation of allowedness and φ, and both averaged sign bounds are proved. The off-image argument uses the inverse permutation correctly.
* `Certificate.lean:6–7`: exact fifteen-coordinate ordering and insertion of ∅; this is the full constant-1 face used in the ordinary proof. Lines 8–83 establish the orbit equalities by genuine permutations, not asserted lookup facts. Lines 84–141 verify the nine meet/join identities, two good witnesses, two bad tests and final arithmetic. Lines 142–145 specialize the universal existence assertion at d=5,r=2 and print the endpoint's axioms.

Dropping polynomial-time evaluation enlarges the candidate class. Refuting this stronger bare-existence assertion therefore refutes the source assertion. The coordinate-model equivalence above is a semantic review; no claim is made that the packet formalizes computational complexity or a separate cardinality-to-Fin n bijection.

`bash scripts/replay.sh` independently rebuilds each module in a separate process with Lean 4.34.1, `-M3500 -j2 -DwarningAsError=true`, then invokes **leanchecker -M3500 -j2 Certificate**. Imports use the specified read-only pinned mathlib cache; no upstream rebuild was attempted. `logs/replay-final.log` records all five strict modules plus checker PASS. I added `ReviewAudit.lean`: it rejects local axioms, unsafe/partial definitions, unsafe opaque constants, and any transitive axiom outside the whitelist. All **45** local declarations pass. The final endpoint depends only on **propext, Classical.choice, Quot.sound** (`logs/lean-ReviewAudit.log:1–3`). Source scanning found none of sorry/admit/axiom/unsafe/partial/implemented_by/extern/_unsafe_rec/native_decide/ofReduceBool in the two proof sources (`logs/source-scan.log`, empty). The first independent audit had a count-type inference error; its final corrected strict run passes.

## D. Prior art and subsumption — material new finding

A [2021 paper by Elbracht, Kneip and Teegen](https://arxiv.org/abs/2103.13162), *The Structure of Submodular Separation Systems*, defines order-induced submodularity by P={a:f(a)<k} (`structure.txt:253–256`). Its Section 4 defines a dependency digraph, proves strict decrease along its edges (Lemma 4.1, lines 452–469), and excludes directed cycles (Corollary 4.2, lines 474–475). This is directly applicable to our family on the constant-1 face. In particular, its partial-lattice statement does not require the symmetric order function used elsewhere in that paper.

My independently constructed dependency graph has 32,768 vertices and 1,003,665 distinct nontrivial outer edges. It is cyclic. `known-criterion-cycle.json` and `logs/subsumption-final.log` give this explicit cycle; each c is good, while a, b and the other meet/join point are bad:

| a | b | good c | a∩c | a∪c |
|---:|---:|---:|---:|---:|
| 103 | 5743 | 5646 | 6 | 5743 |
| 5743 | 1067 | 19899 | 1067 | 24575 |
| 1067 | 5359 | 4301 | 9 | 5359 |
| 5359 | 103 | 11127 | 103 | 16383 |

Each row immediately implies f(b)≤f(a)−1: apply submodularity to a and c, use f(c)≤−1 and nonnegativity of the other meet/join point. Adding gives **0≤−4**, without symmetrization. Thus the candidate's nonexistence conclusion is an instance of this already published obstruction criterion once this concrete cycle is identified. Do not claim a new general separation obstruction or mathematical necessity of the 13-row proof. Conversely, the paper's general criterion alone does not state a counterexample to Conjecture 3.33, and I found no occurrence of this family or citation to Brakensiek–Gopi–Guruswami there. Whether this newly identified finite application passes the campaign's exclusion of routine corollaries is a substantive credit question, not something the kernel can resolve.

Other primary bodies checked:

* [Nägele–Sudakov–Zenklusen](https://arxiv.org/abs/1707.06212), Theorems 1.1, 1.2 and 1.5 (`nsz.txt:187–275`), concern prime-power modular algorithms and obstruction set systems, not this sign-family realization.
* [Nägele–Santiago–Zenklusen](https://arxiv.org/abs/2109.03148), latest listed v3, studies TU constraints and reduces special blocks to congruency-constrained submodular optimization (`tu.txt:1856–1972`); no statement resolving this conjecture was located.
* [Nägele–Nöbel–Santiago–Zenklusen](https://arxiv.org/abs/2302.07029), `advances.txt:166–195,335–345`, treats strictly modular IP feasibility and group-constrained lattice feasibility. It does not establish a separator for arbitrary monomial images.
* OpenAlex live title search found STOC W2913322957 and journal W4280572229. The citing-work filters returned respectively two and one records: *Turán numbers of sunflowers*, *CNF Satisfiability in a Subspace and Related Problems*, and *On the Congruency-Constrained Matroid Base*. The latter two bodies were fetched (`cnf.txt`, `matroid.txt`); the first is not a source on the separation statement. These sparse indexing results cannot certify exhaustive citation coverage. The checked later papers and fresh author listings supplied no explicit public refutation/withdrawal.

Three spaced unauthenticated GitHub **repository** searches ("submodular separation", "1902.04740", "Brakensiek" "submodular") each returned zero repositories. This is not a code or full-text search. Live Lean Pool HEAD is **01db1d7049cf9668bda1e9e106875ee1278b43e6**, dated October 7, 2026. The first root-level projects.yml request returned 404; the complete nontruncated tree located **LeanPool/projects.yml**, which was fetched at that commit. All ten candidates/ files were fetched and screened, along with projects.yml. Seven keyword hits concern unrelated polynomial/Demazure projects (`registry-matches.json`); no matching separation proof was found. HTTP receipts and hashes are under `downloads/*/receipt.json`, with full registry and citation logs under `logs/`. This bounded screen is not global novelty clearance. Denied Crossref, Semantic Scholar, arXiv API, ScienceDirect and SIAM PDF routes were not retried; no TLS verification was disabled.

## E. Recommendation and exact hold conditions

At (r,d)=(2,5), n=16, neither an endpoint convention nor an asymptotic loophole explains away the counterexample in the preprints. The constant coordinate is treated correctly, and the source's proposed hardness approach really assumes the false assertion. Small exact counterexamples are eligible in principle under the brief. The result does not settle modular submodular minimization itself.

**HOLD, with zero acceptance/credit.** Required before root can proceed:

1. Read the final journal section (or establish an accepted manuscript's equivalence) and determine whether Conjecture 3.33 was retained, restricted, replaced or withdrawn. The current evidence does not answer this.
2. Resolve the routine-corollary exclusion explicitly using the 2021 Lemma 4.1/Corollary 4.2 and the four-edge cycle above. The application to F_{2,5} may still be a new finite counterexample, but an acceptance argument must not present the general obstruction as new. If root regards this direct finite application as routine under the campaign rules, **EXCLUDE** it rather than enlarging the formal certificate. No additional Lean work would repair a novelty exclusion.

The four-edge alternative is reviewer evidence and has not been formalized here; the independently replayed original Lean theorem already establishes the exact negation. Root alone adjudicates acceptance.

## Integrity, reproducibility, and limits

`inputs-before.sha256` binds the candidate, summary, results, packet, compressed data and discovery verifier before substantive checks. Candidate SHA256 is **36bdc4e2b15ef0ba6a62201088aaea9343b0f0c0fdc4a28d85ad0fa666a050e4**; packet SHA256 is **441cb79ec825366931cdee6221b99e4b3235dd2145f343565e8df2fb2bd13db8**. `extra-before.json` binds additional source and Lean inputs before extraction review. `expanded-before.json` and `expanded-after.json` contain the final 45-input inventory; the exact independent mathematical verification was repeated between these snapshots. Original initial hashes and all expanded hashes agree (`logs/integrity.log:1`). Download bodies are bound by their individual receipts. Tool binaries are hashed in `logs/tool-hashes.sha256`.

Own scripts: `scripts/capped.sh`, `prepare.py`, `mathcheck.py`, `subsumption.py`, `fetch.py`, `integrity.py`, and `replay.sh`; independent Lean audit: `build/fresh/lean/ReviewAudit.lean`. All local Python invocations used real script paths with `python3 -I`. Every Python, Lean and checker process ran through the lane-local RSS watchdog with two CPU affinity, CPU 120 s, wall 140 s, 6 GiB sampled process-group RSS limit, and MALLOC_ARENA_MAX=2. Every Lean invocation had -M3500; heavy processes ran serially. Early cap calls enforced limits but did not retain peak receipts; the final repeat added `logs/cap-*.json` exit/RSS/wall receipts. No software installation, child agent, git operation, shared-ledger edit, browser tab, upload or external message occurred. All write paths were lane-local. All spawned process groups completed; no background jobs remain.
