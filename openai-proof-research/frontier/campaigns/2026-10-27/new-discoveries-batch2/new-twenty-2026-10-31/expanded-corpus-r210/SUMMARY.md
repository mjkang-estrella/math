# expanded-corpus-r210 — research disposition

No new solution or qualified candidate was established. Credit claimed: **0**. No Lean packet was produced because no new full-scope theorem survived the mathematical and prior-art checks. This is a documented screening/search pass, not a claim of complete literature coverage or completion of the campaign goal.

`results.json` contains exactly the 20 reserved IDs, their literal statements, chunk paths, one-based line numbers, raw-line/chunk/statement hashes, primary-source hashes and HTTP receipts, review depths, attempts, and remaining gaps. Exact raw corpus lines, including their original newlines, are in `sources/<ID>.jsonl`. The original reservation and task remain intact.

## Source-backed exclusions

Eight records should not be rediscovered:

- **342444, 342445:** Ciolan's own Theorems 2 and 4 prove the inequalities; previously known identities supply the equalities. The abstract's “6 and 10” means moduli, not two tested sizes. Source theorem statements and the proof's generating-function/asymptotic argument were inspected.
- **343122:** The source's introduction explicitly reports prior proofs of Lin's congruence by Chern, Gireesh–Naika, and Lin–Wang–Xia. The cited proof bodies were not independently replayed; this is a source-reported prior-resolution exclusion.
- **340100:** Xiong–Zang prove the intended Chan–Mao conjecture. The MathDB backward-size version shifts the source's exceptions incorrectly. Such a correction earns no credit.
- **336512:** The exact inequality, not merely eventual Jensen hyperbolicity, is Larson–Wagner, arXiv:1904.12727, Theorem 1.2. Its proof handles n>900 by explicit error estimates and checks the remaining finite cases. The original source's Conjecture 1.2 is distinct from its proved Theorem 1.3; the later exact theorem is decisive.
- **338207:** Greaves–Syatriadi–Yatsyna, arXiv:2104.04330, Theorem 1.1 and Section 2 construct 57 equiangular lines in dimension 18. The paper explicitly identifies this as a refutation of Lin–Yu's proposed 56. The reserved conjunction is already false.
- **338978:** Brettell–Semple–Toft's classification, arXiv:2409.13834, Theorem 1.3, explicitly resolves the original graphic Conjecture 7.6 and identifies its missing exceptional families. Printed exceptional graphs are not new counterexamples.
- **336099:** Schreib's September/October 2026 paper, arXiv:2610.00086, gives a 16-vertex disconnected cubic counterexample and a public Lean development at `jamesschreib/wormald-conjecture`. The parity proof, padding corollary, and stated formal endpoints were read. This lane did not rebuild that public development. The connected case is a different target.

## Exact computations

All searches below ran sequentially under `scripts/cap.py`: at most two CPU cores, CPU limit 120 seconds, wall limit 140 seconds, 6 GiB address-space limit (thus also a conservative RSS ceiling), and `MALLOC_ARENA_MAX=2`. Each process completed successfully. Full stdout and command/resource records are retained in `outputs/`.

| Reserved ID | Precisely covered search | Outcome |
| --- | --- | --- |
| 341836 | Complete BFS of signed prefix-reversal balls at n=26 and n=27 through distance 5 | Fifth spheres 9,404,200 and 11,460,150 match Conjecture 6.1(i). This extends the source's k=5 table beyond n=25, but proves none of the infinite five-to-nine-flip formulas. |
| 340018 | Every irreducible character row and every even-parity reverse-lex initial prefix, separately for n=21 through 30 | No negative Schur coefficient. At n=30, 5,604 rows and 2,811 distinct even prefixes. Source reports verification only through 20. |
| 374163 | Exact integer coefficient products through degree 3,000 for the parity difference and distinct-part partition series | No violation for 11≤n≤3000; least gap 1 at n=14. |
| 337567 | All labeled loopless digon-free oriented graphs through order 6, retaining precisely equal in/outdegree at every vertex | Eulerian counts at orders 1–6: 1, 1, 3, 15, 219, 7,839. No negative total-neighborhood gap. |
| 337567 | Seed 210, 1,000 unions of compatible directed cycles at each order 8,12,16,24,32,48,63 | No violation among 7,000 samples. These samples are not exhaustive or uniformly distributed. |

The character implementation uses beta-number rim-hook removal and Murnaghan–Nakayama recursion. An independent consistency check verified hook-length dimensions and weighted character-row orthogonality exactly through n=9. The finite computations remain diagnostics, not formally certified theorems or proofs of the unrestricted claims.

## Mathematical routes and gaps

**340018:** The source's omega-symmetrization shows how the stronger initial-segment positivity conjecture would imply this parity version. That implication does not prove either claim. The full-row computation reached n=30 without a negative coefficient. A general positivity mechanism or a larger exact obstruction remains absent; larger character tables alone offer no uniform proof.

**374163:** If A(q)=∏(1+2q^k)/(1+q^k) and Q(q)=∏(1+q^k), the precise missing lemma is [q^n](Q−A)>0 for every n>10. The exact recurrence `(1+q^k) A_new=(1+2q^k) A_old` gives the reported finite check. The identity A/Q=∏(1−q^(2k)/(1+q^k)^2) suggests an alternating expansion, but its coefficients are not manifestly nonnegative. No sign-reversing injection, uniform positive expansion, or explicit analytic remainder bound was obtained. Aniceto–Ballantine's 2026 citing paper proves related source identities; its inspected scope is not a proof of this inequality.

**341836:** Plain BFS pushed the five-flip component past the source range twice. The source's classification of 8- and 9-cycles alone does not establish all length-five-through-nine sphere formulas. A proof would need a complete geodesic-equivalence enumeration or a sound strip-compression theorem. Neither was established. Larger radii at the required n have a much greater memory cost.

**337567:** Small exhaustive cases and cycle-union samples do not extend Cary's restricted simple-cycle-intersection theorem to arbitrary Eulerian digraphs. Repeated second-neighbor collisions are the unresolved obstruction to a uniform counting argument.

**340796:** There is an elementary matrix subcase: if A is an invertible 8×8 sign matrix and each single-entry flip changes |det A| by ratio 3/4, put c_ij=A_ij(A⁻¹)_ji. The determinant lemma forces c_ij∈{1/8,7/8}; the row identity ∑_j c_ij=1 forces every entry to be 1/8. Thus A⁻¹=Aᵀ/8 and A is Hadamard. This is a short bridge from elementary determinant facts and the classical determinant bound, not a significant discovery. Moreover, the full source vertex/chart semantics must be checked before identifying this with its blind-decoding statement. No full-source solution is asserted.

The remaining records **343811, 338906, 339565, 340345, 381419, 336435, 343632** have source-backed parked entries with explicit gaps. No exhaustive search was run for them: no feasible source-faithful beyond-verified-range certificate mechanism was established. In particular, period numerics cannot prove unequal periods; small binary-sequence enumeration repeats a large known nonexistence range; an additional cycle-design instance would not prove an all-m statement; and abelianization agreement cannot certify group isomorphism. These omissions are explicit limitations of this pass.

The raw references for **343811** say “refuted,” but the actual source retains reserved Conjecture 37. This lane does **not** propagate the annotation as a proved refutation of that statement. Its k=2 case is the Four Colour Theorem and the source describes verification through k=7; the general target is parked.

## Prior-art and access audit

`outputs/history-screen.json` records the ID search across historical SUMMARY/CANDIDATE/results/ledger files. The only hit was the root's launch note for this lane; this does not establish global nonreview. Ancestor AGENTS files, the ledger and inherited accepted/excluded-family context were consulted. No protected family was taken over.

Live public registry heads were obtained with `/commits/HEAD`:

- Lean Pool: `01db1d7049cf9668bda1e9e106875ee1278b43e6`.
- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.
- Omega: `e0da8fcc80226febc4e7ea0836927bc71d158292`.

Lean Pool's complete tree, actual `LeanPool/projects.yml` and all candidate-directory files were fetched and screened. The root `projects.yml` request returned 404; the tree supplied the actual location. OpenAI and Omega whole-repository recursive responses were truncated, so separate complete preprints and D5/Problems subtrees were fetched. These were catalogue/path screens, not full proof-body audits. GitHub repository queries are preserved in `outputs/github-search.json`; eight spaced queries returned zero hits, which is only a bounded non-finding. The Wormald proof was found by the literature search despite the repository search non-finding.

Dated raw HTTP bodies and status/header/SHA256 receipts are append-only in `receipts/`. Web search outputs 02–10 are also saved. The first exploratory web-search response was not separately serialized; the resulting primary source downloads do have independent receipts. No denied service was used intentionally, no denied HTTP request was retried, no TLS verification was disabled, and no browser or external message was opened/sent. Search-engine snippets mentioning denied hosts were not followed. No Crossref, Semantic Scholar, arXiv search API, ScienceDirect, or DBLP page was fetched directly.

All downloaded material was treated as data; no downloaded script was executed and no archive was extracted. Python scripts ran with `python3 -I` and `PYTHONDONTWRITEBYTECODE=1`. Source conversion used `pdftotext`. A local C++ alternative was written but not run because `g++` is absent; the actual Eulerian experiment is the capped Python implementation. No package installation, git operation, ledger edit, child agent, or out-of-lane write was performed by this lane.

Absolute novelty, current MathDB comment/solution state, and all inaccessible/unindexed literature are not certified. Known source results are exclusions, bounded non-findings are parked, and no discovery is self-accepted.
