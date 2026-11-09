# Expanded corpus r187 research report

Lane: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r187`.

Twenty reserved IDs have individual entries in `results.json`, with exact literal
statements, preserved raw corpus lines, one-based line numbers, chunk/raw/statement
hashes, source receipts, review depth, mathematical attempts, and remaining tasks.
No discovery credit is claimed. Five entries are excluded or recommended for
exclusion; fifteen are parked. This is a bounded research pass, not a claim of
exhaustive technical or worldwide literature coverage.

The concrete finding is a refutation of **340386**, Beelen–Ghorpade Conjecture
2.5(3). For q = 2, ell = m = 4, t = 2, the code weights are
3200, 3776, 3808, 3760. The fourth is below both the second and third.
An independent exhaustive traversal of all 65536 binary matrices confirms the
weights, without using the source weight formula. There is also an ordinary
proof from that formula, and an infinite square-binary family at t = 2.
See `CANDIDATE.md` for the proof, exact meaning, and credit analysis.

**Verdict: recommend exclusion from campaign credit.** Both the example and its
infinite extension are a few-line evaluation of the source's established
Delsarte formula, explicitly disallowed by the binding brief. No exact prior
counterexample was located in the bounded searches, but absence of a located
counterexample is not novelty clearance. Root retains adjudication. This is not
presented as a strong credit-qualified lead. No Lean packet was manufactured:
there is no proved literal Lean endpoint, and no eligible strong lead survives
the source-ingredient gate. The ordinary proof and diagnostic scripts remain
available for review.

Other exclusions are 336184 (source Theorem 2.9 already proves it), 341203
(later arXiv source explicitly cites the negative list-multiplication resolution),
371761 (source explicitly reports Zheng–Sun's published disproof), and 335236
(the literal paraphrase and printed GRP bounds have source-scope/internal
consistency defects; correcting them earns no credit). The original 335236
source requires products of distinct formal roots, not arbitrary polynomials.

## Actual computational coverage

All numerical searches below ran serially under `scripts/limited.py`, with
2 CPUs, CPU limit 120 seconds, wall watchdog 140 seconds, sampled process-group
RSS watchdog 6 GiB, and MALLOC_ARENA_MAX=2. All 13 capped invocations finished;
no process was killed and no background numerical work remains.

- **340386:** 19894 tuples with q in {2,3,4,5,7,8,9}, ell from 3 through 30,
  m from ell through ell+6, and 2 <= t < ell. Found 352 failing tuples, all
  binary square cases within that finite sweep. Independent direct enumeration
  at q=2, ell=m=4, t=2 as described above. No full classification asserted.
- **336183:** every unlabeled free tree on 2 through 14 vertices; every
  +/-1 edge orientation modulo global sign, including all tied variance
  maximizers. Total 16323363 assignments. No failure of either the central
  distance identity or the nonpath degree-at-least-three requirement.
- **341192:** all 14457 rooted tree shapes with no unary vertices for maximum
  outdegree d in {2,3,4}, through 11 leaves. Every k from 2 through n checked
  against the recursively even tree. No counterexample. A separate exact
  dynamic program optimizes binary targets k=4,5,6 for every n <= 1200;
  no improvement over the even tree. Larger targets require shape-sensitive
  Pareto states; the scalar recurrence is not asserted for them.
- **340667:** all connected bipartition-labelled graph presentations on 2,4,6
  vertices and all binary weight assignments. Counts respectively 1,6,271
  presentations and 4,96,17344 weighted instances. Seeded order-eight sample:
  166 connected presentations, 5312 binary weighted instances. No loss for
  Alice. This does not cover arbitrary real weights or all order-eight graphs.
- **341161:** all numerical semigroups through genus 18, 33281 nonzero-genus
  objects, with every depth cutoff 2 <= d <= g+1 tested. No growth violation.
  The first diagnostic invocation had an empty-root generation bug; its log
  is retained as `logs/semigroups.log`, and is invalid coverage. The corrected
  run is `logs/semigroups-fixed.log`; the corrected table has n_18=13467.
- **335825:** dimensions 1 through 32, composite q <= 1000, both unit-cube
  indicator and constant-one weight functions. 53184 family/dimension/q
  cases, no composite passing every divisibility test. Arbitrary weight
  functions are not covered.
- **336371:** full I_p counts for every prime <=500. Beyond the source's
  reported 100000 bound, connected parameters a=97,5,297 were found for
  p=100003,100019,100043, respectively. These are existential witnesses,
  not exhaustive counts at those larger primes.
- **335659:** 2000 seeded multiplicity trials on Petersen support, with
  multiplicities 1 through 5. Only 23 met all degree requirements for
  a,b >=2; all 23 admitted a feasible partition. This is a narrow diagnostic.
  Source maximum multiplicity was used rather than the incorrect paraphrase.

The existence-of-threshold statements 335494 and 365342 cannot be refuted
by a single bounded graph. The deep design, polytope and analytic targets
were disposed without expensive blind computation. 340348 was parked after
source/family checks, rather than treated as a new stable-Kneser-family credit.
No positive finite test is used as a universal proof.

## Sources, searches and registries

All 19 distinct source arXiv submission-history pages were retrieved, and all
29 listed versions were downloaded into fresh directories and converted to
text. Source definitions and relevant neighboring claims are recorded in
`outputs/source-excerpts.json` and in the individual result entries.
Publisher coverage is partial: the tree version of record was downloaded;
matroid and projection publisher material was inspected through web responses;
the code author-copy download and web open timed out, although indexed
publisher-layout excerpts retain the exact conjecture. Several other publisher
bodies were not obtained. Those gaps block a novelty-qualified candidate,
and are not presented as completed publisher comparison. Source-only
resolution reports are distinguished from independent reconstruction of the
cited proofs.

Literature and later/citing-work searches preceded every exhaustive search.
Stored web responses include title/arXiv queries, more precise topic queries,
2026-related successor searches, and exact-weight counterexample searches.
These are search-result neighborhoods, not a complete citation-index traversal.
No accounts, browser tabs, uploads, author contacts or external messages were
used. No TLS verification was disabled. The direct HTTP helper records every
attempt in a new directory and guards redirects to denied hosts.

Current registry heads:

- Lean Pool: `01db1d7049cf9668bda1e9e106875ee1278b43e6`.
- Omega: `1d46a625e4e90388fb62b944367e1bc5fc51257a`.
- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.

Lean Pool projects.yml and all candidate files were downloaded at the pinned
HEAD. Eight GitHub repository queries were spaced nine seconds apart; all
returned HTTP 200. Initial recursive root trees were truncated, so additional
complete scopes were fetched: Omega D5 (14021 entries), Problems (1741), and
OpenAI preprints (13578). Recorded text/path hits are not proof-reading or
implication clearance. The GitHub queries were broad, and did not combine
all target authors and arXiv identifiers; no stronger registry clearance is
claimed. The weight candidate was excluded before any Lean investment.

## Artifacts and reproducibility

- `results.json`: exactly 20 ID-keyed dispositions.
- `CANDIDATE.md`: ordinary refutation and exclusion recommendation for 340386.
- `outputs/registry-screen.json`: heads, queries, hits, coverage and limits.
- `outputs/source-manifest.json`: hashes for retained source artifacts.
- `outputs/validation.json`: raw/statement hash validation and process receipts.
- `raw/`, `sources/`: original corpus lines, downloaded sources and HTTP receipts.
- `scripts/`, `logs/`, `outputs/`: reproducible scripts, full logs and exact tables.

Run scripts using real file paths and `python3 -I`. Run numerical scripts
through the resource wrapper, choosing a fresh log name because it refuses
to replace a process log. Dependencies and shared files remain read-only.
No git or shared ledger/index changes were made. No Lean invocation was run.
