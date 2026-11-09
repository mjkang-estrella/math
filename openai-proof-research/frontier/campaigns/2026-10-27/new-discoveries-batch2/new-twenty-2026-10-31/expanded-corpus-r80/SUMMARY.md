# Expanded corpus r80 — incomplete research checkpoint

No new qualified solution or Lean endpoint. Credit is zero; the accepted count remains 12/20 beyond the 39 prior results. This is **not a completed multi-hour investigation of all 40 reservations**. All 40 literal records were read and preserved with raw-line provenance, and exactly 40 ID-keyed dispositions are in `results.json`. Several finite-object targets still lack the mandatory exhaustive search and full primary-definition recovery; they are explicitly marked incomplete, rather than novelty-cleared or technically rejected.

All writes were confined to this lane. No child agents, git, shared ledger edits, publication, external messages, uploads or browser tabs. HTTP retrievals have URL, UTC, status, byte count and SHA-256 receipts under `sources/`. Failed requests are retained. No prohibited MathDB/Palomar access retry was attempted. General web search worked in this session; its results are leads, not primary proof substitutes.

## Useful exact exclusions

* **379135:** Kupers–Miller–Patzt, arXiv:2609.12951, Theorem A explicitly proves nonvanishing of every Morita class **and its image in Out**. This avoids the Aut/Out ambiguity in the abstract. Section 5.1 supplies the abelian-cycle proof reduction to Theorem 4.2. This is a September 2026 prior resolution.
* **322957:** Tyler, arXiv:2406.02982, Theorem 1.2 proves Stanton's conjecture; Section 6 separates the proof ranges. The original range excludes `t=N-1`. MathDB's inclusion of this endpoint is an excluded formulation issue.
* **328606:** Keith, arXiv:1502.00366v4, Theorems 1 and 2 prove **both** required congruences. The actual quantities count partitions with a prescribed number of distinct part sizes, despite the MathDB title. The author's 2016 slides and the 2026 follow-up were also located. An initially guessed unrelated arXiv URL saved as `keith2017.html` is not evidence for this conclusion; the correct verified source is `1502.00366.html`.
* **374665 and 374666:** inherited exclusions retained. Chen–Ono–Zhang's actual source gives the old `n=4` binary log-concavity counterexample and proves cyclotomic nondivisibility in Theorem 2.
* **369393:** the exhaustive search exposes only a boundary defect: `n(g,g)=n(g+1,g)=1` for `2<=g<=19`. The authors' own ordinary/stabilizer classifications already imply these equalities. This is excluded endpoint credit; the interior fixed-type conjecture remains unresolved. An initial assertion that *all* comparisons passed was caught by validation before handback and corrected in `results.json`.
* **318905, 332146–332148:** the supplied primary sources already contain the stated refutations. **316166** is explicitly a known theorem. **371953** is explicitly reported disproved by its primary source; the cited refutation was fetched, but its entire construction was not audited here.
* **374660 and 374851** are the same ordinary-partition irreducibility target. They cannot earn separate credit.

## Sustained routes and precise gaps

**374233, interval spectra.** Fixed Definition 2.1 before search: a subset is in general position when no third chosen vertex lies on any *finite directed shortest path* between two chosen vertices. Floyd–Warshall distances identify all forbidden triples, then all vertex subsets are checked. Every orientation is enumerated for each graph input. Results:

* Order 6: all 156 atlas representatives, 141,795 orientations.
* Order 7: all 1,044 atlas representatives, 12,490,035 orientations.
* Orders 8, 9 and 10: 100 deterministic sampled graphs at each order, with 10–16 edges; all orientations for each input. Exact input lists and totals are in `outputs/gp-coverage.json`.

No spectrum gap. The source states computation through order six, so the order-seven sweep goes beyond that reported range, but remains diagnostic. The obvious proof via one-edge reversal fails: atlas graph 59 (a four-vertex path plus two isolated vertices) has orientation mask 1 with gp=4, and reversing edge 2 gives mask 5 with gp=6. An independent BFS/subset checker verifies both. Thus the missing theorem is a **global interpolation** result; local edge-flip Lipschitz continuity is false. No larger counterexample or proof emerged. No formal endpoint was manufactured from these bounded computations.

**374660/374851, partition numerator irreducibility.** Recovered the literal polynomial using monic lcm `L` of every subsum polynomial and `num = sum L/sp(lambda)`, equivalent to the authors' `sum h_lambda / gcd(h_lambda)`. Enumerated every partition and factored the exact integer polynomial for **2<=n<=22**. Every completed polynomial is irreducible. The `19..24` process reached the CPU limit while working beyond 22; no coverage of 23 or 24 is claimed. The paper's coprimality theorem only removes cyclotomic factors. Palindromicity and the transform `x+1/x` alone do not exclude non-cyclotomic reciprocal factors. A uniform irreducibility argument is still missing; `n=1` is only an excluded constant-polynomial endpoint issue.

**382240, cup stacking.** Recovered source move semantics: both source and target piles are nonempty, and source pile size equals graph distance; the whole pile moves. A target pile cannot move in a successful play because an empty target can never be refilled. DFS uses this sound restriction and rejects a non-target pile larger than its eccentricity. At height three, root and depth-two representative targets have independently replayed move certificates. Depth-one and depth-three targets hit the 200,000-state cap; they are **not** counterexamples. This does not even reproduce all known height-three cases. A useful next mechanism would be subset-pile dynamic programming or distance-respecting stacking partitions, not a larger unstructured DFS. No new height was settled.

The numerical-semigroup route was also pursued through exact genus/type enumeration and the source's shift injection. That injection changes type as well as genus and cannot prove the desired fixed-type inequality; the only failed inequalities were the already implied diagonal endpoint equalities.

## Other bounded searches

`outputs/` preserves complete data; scripts and process receipts are under `scripts/` and `logs/`.

* Strong target pebbling: all connected atlas graphs of orders 1–4, all targets of total demand 1–3, complete recursive reachability and exact pebbling thresholds; no violation.
* Numerical semigroups: complete semigroup tree through genus 20 (37,396 at genus 20); fixed-type interior comparisons through genus 19 pass. Diagonal equalities are documented above.
* Cordial trees: every unlabeled tree of orders 2–8 for cyclic groups of orders 2, 3, 4; exhaustive balanced label assignments until a witness. This does not address all finite Abelian groups or establish weak cordiality.
* Curling sequences: all binary words over `{2,3}` of lengths 1–12, plus each prefix by 2 and 3, tail cap 500; no cap failures and no doubly rotten word. Source coverage through length 34 is stronger.
* PQS: all permutations through size seven, all block-reversal cuts as needed, exact 231 avoidance; sortable counts `1,2,6,24,120,685,4148`. The intended finite-basis claim is distinguished from the source's defective finite-class wording.
* Self-conjugate/core partitions: explicit partitions and hook lengths through size 30. Conditional GRH resolution of self-conjugate six-core positivity was found, not an unconditional proof.
* Partition congruences: exact dynamic programming for at most three distinct part sizes through argument 2000; both required congruences pass every covered `36n+30`.
* Claw-free list coloring: every claw-free atlas graph through order four, every chromatic-number-sized list assignment from a four-color palette; no witness. Arbitrary palette size remains untested.
* Shifted primes: all pairs `1<=y<x<=300`, witnesses retained. Squares: all 4,095 nonempty subsets of the first twelve positive squares, exact sumset sizes and ordered additive energies retained. Neither sweep tests unspecified asymptotic constants or infinitude.

## Registry and literature limits

Live `/commits/HEAD` receipts give OpenAI `4eaee87548250b2682affda7d05d947c05554bae` and Omega `4c7a89d97001d86901a192a7d002be32def54ac3`. The Omega head changed from the task snapshot. Its current complete, non-truncated D5 and Problems recursive trees were fetched (13,350 and 1,637 entries respectively); no reserved ID occurs in their paths. This is **only an ID-path screen**, not proof-body clearance. The unchanged OpenAI head allows reference to the inherited complete preprint listing; no exhaustive new body review is claimed. Author/journal/data checks remain incomplete for multiple unresolved IDs, especially the 1-planarity construction, Type BII normalization, cohomology complex, signed-flow and embedding searches.

No claim of worldwide novelty. No Lean packet, strict replay, leanchecker run, local declaration audit or upstream rebuild is claimed because there is no genuine endpoint to certify. `outputs/validation.json` checks the 40-entry artifact shape, literal hashes, selected known enumeration totals, exact diagnostics, independent edge-flip calculation and cup-move certificate replay. These are diagnostics only.

The requested full pass remains unfinished. Outstanding finite searches are enumerated explicitly in `results.json`; they must not be silently treated as covered. No research process was left running at handback.
