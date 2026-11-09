# expanded-corpus-r221 handback

**No qualifying new solution. Six reserved targets excluded by prior exact results; fourteen parked. Credit requested: 0. No new Lean endpoint.**

The required twenty ID-keyed entries are in `results.json`, with literal statements, chunk/line/raw/statement hashes, source receipts, review depth, mathematical attempts and remaining gaps. `CANDIDATE.md` explains the strongest reproduced hit and why it is excluded.

## Main findings

| ID | Disposition | Decisive evidence |
|---|---|---|
| 367655 | Excluded | Source already refutes Pruesse–Ruskey for non-simple Venn diagrams |
| 367789 | Excluded | Source proves the chromatic torsion conjecture |
| 367794 | Excluded | Fox–Tidor SoCG 2026 Corollary 3.9 strengthens the exact conjecture |
| 367832 | Excluded | Source Theorem 4.3 proves the finite obstruction equivalence |
| 368314 | Excluded | Reproduced 73-state `[3] × [12]` nonzero orbit; exact prior public Lean refutation dated 2026-10-04 |
| 368492 | Excluded | Lean Pool public common-neighbour refutation for every base size |

The rowmotion hit is a real refutation but not new. It was independently reproduced by a C search and a separate Python verifier using full interval tests. The public theorem was found before any Lean formalization. Neither the independent rediscovery nor a parameter extension is eligible for credit.

## Exact numerical coverage

| Route | Coverage | Outcome |
|---|---|---|
| Rowmotion | All interval-closed sets at `[3] × [4,6,8,10]`: 321, 1,702, 6,349, 18,811 states | All orbit sums zero |
| Rowmotion | `[3] × [12]`, first nonzero orbit; independently verified 73-state cycle | Sum +1; already public |
| Three-colour matchings | Complete connected-union coverage at orders 12 and 14: 13,166 and 175,641 connected representations | Every n-1 colour profile attained |
| Three-colour matchings | Order 16: 423,447 connected representations in one partial cycle type; random samples through order 24 | No hit; incomplete coverage |
| One-crossing triangulations | Five sampled spheres of orders 30,30,32,36,40; 474 raw edge additions | All 4-colourable; every SAT model checked |
| Perfect divisibility | All 1,253 atlas graphs through order 7 | All perfectly divisible |
| Perfect divisibility | 4,883 G(n,p) samples at n=8,...,13, p=.2,.4,.6,.8 | All perfectly divisible; no P5-free violation |
| Klein grid quotients | Ten cases, including 1,394 and 1,426 faces | No face-transitive case in this family |
| Latin partitions | Six realizations, orders 11,12,15,18,17,20 | All constructed and directly verified; instances only |

## Parked targets

367410, 367548, 367636, 367774, 367788, 367984, 368114, 368164, 368169, 368265, 368277, 368382, 368836, 368837 remain unresolved in this lane. Detailed obstacles are in their entries. Eventual bounds, unboundedness, unspecified-degree rational interpolation and chi-boundedness were not misrepresented as finite falsification problems. The generic rigidity target was not confused with special flexible polytopes. The ordinary cycle-double-cover theorem was not substituted for its five-member strengthening.

## Sources and registry scope

- Exact raw corpus lines including newline are retained under `raw/`; `extracted.json` binds the one-based source line and three hashes, plus each chunk hash.
- `sources/` contains primary HTML/PDFs and immutable dated HTTP receipts. Version histories for all 18 source papers were fetched. Several route-specific version sets were also fetched; not every older body was audited.
- Current registry HEADs: Lean Pool `01db1d7049cf9668bda1e9e106875ee1278b43e6`, OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`, Omega `9cef6d1bafb3f2f5a8cfe59dd73b95e00f78b8a7`.
- Complete Lean Pool tree, Omega D5/Problems trees and OpenAI preprints tree were screened. Global Omega/OpenAI trees were truncated; complete relevant subtrees were fetched separately. Positive Saxl/rowmotion bodies were read. This is not an all-registry-body audit.
- Eight spaced GitHub repository queries plus one targeted follow-up are receipted. Broader literature/citing searches are preserved in `outputs/web-search-*.json`. Search non-findings do not certify novelty.
- Historical ID/title checks, read-only ledger hashes, printed-example locators and source availability are retained in `outputs/`.
- No requests were made to the denied Crossref, Semantic Scholar, arXiv search API, ScienceDirect or DBLP routes. No TLS verification bypass, denied-host redirect, browser tab, external message, child agent, git command or shared-file edit was used.

## Reproduction and limits

Own scripts are in `scripts/`. Every numerical search and SAT call used `scripts/limited.py`: affinity to two CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS guard at 6 GiB, `MALLOC_ARENA_MAX=2`, with one heavy process at a time. The order-16 matching search stops itself at 100 seconds. Full logs and process receipts are in `logs/`. The RSS monitor is sampled and process-local, not a cgroup/transient-peak guarantee. Very fast solver calls can finish between samples. No process exceeded the caps observed by this monitor.

The provided Lean-distribution `leanc` compiler and CaDiCaL were used read-only. Initial ordinary compiler/header attempts failed; those logs are retained. No packages were installed. No numerical diagnostic is described as kernel-certified. Since no new eligible endpoint survived, no Lean rebuild, leanchecker replay or axiom audit was run.

Use fresh output names/directories for replay: raw HTTP receipts must not be overwritten. This is a bounded research pass, not a claim of exhaustive historical or literature coverage or a completed solution to any parked record.
