# fresh-corpus-r16 — research handoff

**New full-scope Lean solutions: 0. Accepted credit claimed: 0.** Campaign baseline remains the root’s1/20 beyond39 historical outcomes. No ready candidate packet, paper, independent review, strict extracted Lean replay or transitive axiom audit is claimed. All writes are confined to this lane; reservation preserved. No children, git, external messages, browser tabs, publication or uploads were used.

## Coverage and evidence

All40 reserved literal records were read, with statements and provenance in `literal-records.jsonl`, `corpus-provenance.json` and ID-keyed `results.json`. Raw-line hashes include the original newline; chunk hashes cover complete original chunk bytes. Exact original source-name/URL/retrieval metadata remain in the raw records. `results.json` distinguishes literal review (40), primary-passage review (14), and specifically named selected proof bodies (5 records). Downloading a body is not recorded as reading its proof. This is not exhaustive technical/literature review of all40.

Ancestor AGENTS, both campaign ledgers, parent prior-campaign-context, upstream pin and catalogue were read. Input hashes are in `context-pins.json`. The bounded old-note search (`historical-note-search.txt`) used exact reserved IDs in Markdown, result/rejection/context JSON and ledgers across the old campaign, excluding this lane. Its matches were the new reservation listings; no earlier technical rejection for these IDs surfaced in that search. This does not clear unindexed notes or other naming schemes. The explicit old exclusions, held330264/335230/326640 and active333569 were respected; none was duplicated.

Current OpenAI/math head was fetched07:40:39UTC Nov1,2026: `4eaee87548250b2682affda7d05d947c05554bae`. Verified hashes of inherited05:55UTC complete-preprints-tree receipts were reused because the head is unchanged. `registry-screen.json` records exact terms/path hits. This is only a path screen; it does not clear all manuscript bodies. The root recursive tree is truncated and was not used as a complete catalogue. Inherited MathDB403 and Palomar403 were not retried or bypassed. Search engines surfaced indexed MathDB text, but that is not direct successful site access or a primary proof source. Public primary HTTP downloads, versions, dates and hashes are preserved in `sources/receipts.json` and `source-versions.json`.

## Substantive findings

**336116 is already solved.** Actual Jones2020 `arXiv:2009.09616v1` Theorem4.3 plus Proposition4.4 prove existence of a star for every powerful order-n set of rank n−1. The star definition gives exactly one lift of each remaining binary vector, hence the precise bijective-deletion conclusion. Original2017, published2018 and successor bodies were compared; complete selected successor proof read. The n7 counterexample MILP timed out without an incumbent, then the n8 run was terminated on finding this direct predecessor. Do not formalize it as a new discovery. [Primary successor](https://arxiv.org/abs/2009.09616).

**336130 remains the strongest unresolved route.** Actual published2020 Conjecture1 remains in the paper. The full problem reduces via its covering theorem to a partition satisfying explicit distance2/distance3 obligations. A reproducible sampled search checked146 qualifying self-centered diameter3 graphs among39002 generated graphs and found a partition for each. A second exact10-vertex diagnostic shows why the published diameter4 greedy initialization fails to establish the needed invariant at diameter3. The remaining obstruction is a simultaneous fixed-neighborhood extension lemma, not an arithmetic or Lean-engineering issue. All reductions, source-version theorem renumbering and failed proof routes are written in `ATTEMPTS.md`. [Published primary body](https://www.ejgta.org/index.php/ejgta/article/download/776/pdf_132).

**335597 remains unresolved.** Exact hook-length squares for paired-row partitions through n80 agree with log concavity, but that entire range was already checked in the original2015 paper. The near-right-end inequality simplifies to a positive shifted polynomial; this is merely an uncredited helper. Source double-hook results and shape-wise inequalities do not imply log concavity of the complete sum. No uniform interior-shape comparison or tableau-pair injection was proved. `ATTEMPTS.md` includes the formulas and precise missing bridge. [Original primary body](https://arxiv.org/abs/1511.08653).

Other exclusions:335849 is explicitly proved by its cited source Theorem2.6;336111 is proved by Li–Wu2017 Theorem2.2 (centroid proof read);336301 is refuted by its own cited paper;336525 is covered by the2022 high-girth STS theorem.336063/336401/336506 already report known resolutions in the literal record or inspected source passage, with limited proof depth clearly stated.335752’s literal O(n³) upper bound is routine.336323 confuses maximum with minimum;335942’s alleged general conjecture was not authenticated in the citedv1 (which has a Haar-trace proposition). No wording/domain fix, special family or newly formalized known result is nominated for credit. All other records have concise individual obstructions in `results.json`.

## Reproduction and resource limits

Run from this lane:

```sh
timeout 30s python tableaux_search.py
timeout 10s python appendage_search.py
timeout 10s python appendage_obstruction.py
timeout 10s python endpoint_algebra.py
```

Scripts now set affinity to CPUs0,1 and virtual-memory ceilings (3GiB for search diagnostics,1GiB for endpoint algebra). The tableaux/appendage searches were freshly rerun with these ceilings; final timing and peak RSS are embedded in their JSON. Tableaux took about8.3s, appendage about0.62s. The powerful first pass used90s solver limits per dimension, two-CPU affinity and HiGHS threads2; its measured n7 peak RSS was231800KiB. That initial pass lacked an explicit address-space rlimit; this limitation is retained rather than retrospectively claiming a cap. Its reproduction script now has a3GiB ceiling, but is **not recommended** because the target is known. HiGHS emitted an options-forwarding warning for threads2; affinity independently bounds usable CPUs. No solver infeasibility output is a kernel certificate.

Toolchain checked read-only: Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; mathlib working-tree HEAD read directly asd13f23b723b8a846827a245b89c10fc7d3f11612. No Lean theorem was written or compiled. Prebuilt-cache trust, strict-warning replay and transitive axiom audits are therefore **not satisfied for a candidate**, not implicitly waived. An exact new endpoint would require all these gates and independent root-arranged reviews before any credit.

`artifact-hashes.json` pins final lane artifacts. `validation.json` checks the40-key reservation equality and the preserved raw-line/chunk hashes. No numerical experiment is promoted to proof and no worldwide-priority claim is made.
