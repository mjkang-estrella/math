# Expanded corpus r211: bounded research pass

**No qualifying new solution. Zero credit. No Lean endpoint.** Four records are excluded by prior work or the current source's explicit report of prior work. One computational refutation is excluded by the user's rule against small modifications of printed constructions. Fifteen records remain parked with specific gaps in `results.json`.

This is a bounded research pass, not a claim that the campaign's discovery goal has been achieved or that every reserved problem received exhaustive mathematical investigation. In particular, the prescribed exhaustive small-instance searches were not implemented for every finitely describable target. Those gaps are explicit, rather than filled with surrogate endpoints. No independent acceptance review was requested or performed.

## Prior resolutions

| ID | Evidence and scope |
|---|---|
| 332319 | Mao, Shi and Zhu, arXiv:2609.23779, Theorem 1.2 states the full Almkvist unimodality result. Current PDF theorem and surrounding proof organization read. |
| 329645 | Black, Drellich and Tymoczko, current arXiv:1501.03238, Section 4.2 explicitly says Wagner disproved alphabet independence. The cited correspondence itself was not retrieved. |
| 331617 | Kim and Lin, arXiv:1706.07208, Remark 5.3 gives precisely the last-entry Entringer interpretation, using their tree encoding and Poupard's result. No index-boundary correction is claimed as new mathematics. |
| 322964 | Alpoge, arXiv:1307.0158, Theorem 11 and its primorial/divisor-sum proof refute all four inequalities eventually. |

The equality-pattern clause of 323267 is also already proved by Lewis and Morales, arXiv:1405.1608, Theorem 3.1. The coefficientwise inequality remains explicitly conjectural in its Remark 4.3; the whole reserved record is therefore parked, not marked solved.

## Exact computations

Every numerical search below ran under `scripts/limited.py`: affinity restricted to two CPUs; CPU 120 seconds; wall 140 seconds; sampled process RSS limit 6 GiB; MALLOC_ARENA_MAX=2; bytecode writing disabled. This is process monitoring, not a cgroup guarantee. Full stdout/stderr and resource receipts are in `logs/`. No Lean process was started.

| ID | Completed coverage | Outcome |
|---|---|---|
| 334721 | Three-run restraints in step-two cyclic order, every positive run-length composition for odd n=5,7,...,17, modulo cycle and colour equivalence; exact polynomial comparison | n=11 improvement, but only one vertex recoloured: explicitly excluded. Independent transfer-DP checks for each integer colour count 3 through 30 agree with both exact polynomials. |
| 329897 | Odd stack counts 7,9,11. Every even token total 12–50 for 7 stacks; 14–120 for 9 stacks; 16–156 for 11 stacks | All first-player wins. These are exact minimax conclusions at the initial empty state, with short-circuit evaluation; not exhaustive evaluation of every reachable state. Eleven-stack run was CPU-killed while attempting 158, before its planned ceiling of 300. |
| 330128 | Every permutation of lengths 3 through 10; 10! = 3,628,800 at length 10; explicit graph isomorphism matching | At length 10: 9,424 distinct labelled competition graphs, 7,362 claw-free labelled graphs, 119 isomorphism types arising from 123-avoiders. No unmatched claw-free graph. |
| 322962 | Every n=63,...,700 and every t=4,...,n-7 | No unimodality violation in integer core-count differences. |
| 328340 | Every integer partition for every degree n=3,...,30; exact symmetric and alternating conjugacy-class sizes, split types included; all-pairs component distances | No diameter above four. Degree 30 has 2,345 symmetric and 1,570 alternating nontrivial distinct class-size vertices; both diameters three. |
| 334269 | Seed 211; 1,000 random labelled graphs at each exceptional order 13,14,16,17,20; edge probabilities cycle through .12,.2,.3,.4,.5; exact power-domination number on eligible graphs and complements | Eligible counts 648,651,724,734,783, respectively. No violation; this sampling is biased toward graphs with small power-domination number and does not settle the exceptional cases. |

The attempted NetworkX competition script failed before any enumeration because NetworkX is unavailable. `competition_plain.py` replaces it with an explicit isomorphism backtracker and completes the stated checks. No package was installed. The excluded odd-cycle calculation, its eligibility objection, and ordinary polynomial derivation appear in `CANDIDATE.md`.

## Sources, registry checks and access limits

Exact corpus lines including newlines are in `raw/`. `extracted.json` records chunk paths, one-based line positions, chunk/raw/statement SHA-256 hashes and the literal statements. Both campaign ledgers and inherited accepted/excluded families were read without edits; their hashes and the bounded historical scan are retained in `logs/prep.log` and `outputs/history-filtered.txt`. Numeric-substring and hash collisions in the raw history scan were not interpreted as old substantive reviews.

Downloaded bytes are retained in `sources/` with immutable per-request `*.receipt.json` files (URL, UTC, status/error, hash). `outputs/http-manifest.json` indexes them. Downloads were data only; no downloaded script was executed. Local scripts run through real paths under `python3 -I`, with PYTHONDONTWRITEBYTECODE=1. No git, child agents, external messages, browser tabs or writes to other lanes were used.

Current public heads fetched in this pass:

- Lean Pool: `01db1d7049cf9668bda1e9e106875ee1278b43e6`.
- OpenAI/math: `4eaee87548250b2682affda7d05d947c05554bae`.
- Omega: `e0da8fcc80226febc4e7ea0836927bc71d158292`.

Lean Pool's complete recursive path tree, pinned `LeanPool/projects.yml`, and every blob in its `candidates/` directory were fetched and keyword-screened. The initial guessed root `projects.yml` returned 404; the tree identified its actual path. Complete Omega D5 (14,062 paths) and Problems (1,758 paths) subtrees and OpenAI preprints (13,578 paths) were fetched separately because both large root-recursive responses were truncated. Keyword hits in these scopes were unrelated; this is a path/metadata screen, not a review of every proof body. Eight spaced GitHub repository searches cover the three sustained combinatorial routes and core/Type-B keywords; exact queries, receipts and returned hits are retained. No matching public proof was identified in these bounded searches; no universal novelty clearance is claimed.

`outputs/arxiv-versions.json` records submission histories. All versions of the Nim, plane-tree and Hanusa–Nath sources were downloaded; the single-version restraint and competition sources were read. Other parked routes received current-version source-body review only, not a complete historical version/citing-body audit. Literature searches, including 2026 leads and citation-neighborhood searches, are retained in `outputs/web-searches*.json`. The initial web batch is documented by the resulting primary downloads and subsequent repeated queries; its raw connector response was not saved. Web connector responses do not expose independent HTTP status/hash receipts, unlike the direct downloads.

No denied service was contacted directly: Crossref, Semantic Scholar, the arXiv search API, ScienceDirect and DBLP remained unused. General search engines may return indexed snippets from these sites; they were not followed as source bodies. TLS verification remained enabled. No 403/429 retries, challenge bypasses or redirects to denied hosts were used.

## Remaining work

No further acceptance work is warranted for 334721: the one-vertex modification is excluded even if it is formalized. The most tractable unresolved routes are the same-order representation theorem for 330128 and a uniform strategy for 329897. Both require new full-scope mathematics, not a larger finite table. The fifteen parked dispositions include analytic, geometric, topological and exact-definition gaps; `results.json` names the missing statement for each ID. No dummy Lean packet was created.
