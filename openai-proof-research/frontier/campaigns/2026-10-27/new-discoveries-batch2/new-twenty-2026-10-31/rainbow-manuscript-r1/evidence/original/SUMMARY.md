# Expanded corpus r144

One candidate is nominated, with **zero accepted credit pending root review**.
Exactly 20 ID-keyed entries are in results.json. Four entries are already proved
in primary literature; fifteen are parked with explicit scope or mathematical
gaps. No shared files or campaign counts were changed.

## Candidate 346167

An explicit 8-vertex graph and its complement are connected and admit rainbow
vertex-disconnection colorings with four and three colors. Their sum is at most
7, contradicting n ≥ 8 in Li–Weng's Conjecture 6.12, arXiv:2004.06285v2.
Version 1 has the identical claim as Conjecture 5.12.

The adjacency masks are [202,225,232,149,232,22,23,31]. The coloring vectors,
112 cut/side certificates, independent Floyd–Warshall check, rigorous ordinary
proof and literal Lean endpoint are all included:

* PROOF.md and CERTIFICATES.md explain the exact argument and bounded novelty review.
* outputs/rainbow-certificate.json is the full finite certificate.
* Semantics.lean: Rainbow.mathdb_346167_literal negates the universal conjecture,
  using actual mathlib connectivity and unbounded walk reachability.
* lean-packet.tar.gz is a source-only, reproducible packet with no local compiled files.
* logs/replay.log and logs/extracted-replay.log retain the clean-source and archive-extracted replays.
* Audit.lean recursively checks axioms of all 168 local declarations, including
  generated instances; the endpoint axioms are propext, Classical.choice and Quot.sound.

The finite certificate has no residual semantic obligations. The source rainbow
condition on S ∪ {x} or S ∪ {y} is proved equivalent to the checker condition,
and the minimum-color invariant is proved to be the least admissible number.
The graph resulting from deleting S and xy is defined by its literal adjacency
restrictions. Cut soundness is proved for arbitrary walks, rather than bounded
BFS. The archive's README records cache trust limits: no upstream rebuild claimed.

Root must independently review fidelity, mathematics, significance and bounded
prior art, and decide acceptance. This is a modest finite refutation, not a
claim to know a replacement bound. Exact individual invariant values are not
needed. No paper was published or uploaded, and no author was contacted.

## Dispositions and computations

Already proved: 346984 (its own Theorem 1.2), 347033 (its own stronger Theorem 5),
348055 (Wu–Zhang Theorem 1.2, published JEMS), and 350736 (September 2026
arXiv:2609.20237 Corollary 1.2).

The first check was 345184 against arXiv:2610.22783. That paper explicitly
disproves the related universal leaf-count upper bound with caterpillars.
However, 345184's own statement already exempts unspecified caterpillars,
spiders and lobsters. Consequently the exact reserved record is parked for
ambiguous exception scope, not falsely declared directly disproved. The
protected full-t-ary-tree candidate 354228 was not taken over.

Sustained bounded searches, with complete scripts and outputs:

* 347559: canonical generation of all 47 nonisomorphic trees of orders 2–8;
  all 1,128 unordered pairs. Exact matching-endpoint domination search found
  no equality witness at the threshold from the source's 3-packing theorem.
* 347594: exact integer subset counts on 360,000 sampled graphs in four
  (n,p) batches: (8,.35), (10,.2), (12,.2), (14,.2). No violation. These
  push beyond the source's exhaustive order-7 range but are not exhaustive.
* 348349: exact coefficients through n=1000 for d=1..100 and every admissible a,
  totaling 5,250 parameter pairs. No negative coefficient difference.
* 345351: 200 dense random digraphs at each order 6,7,8; every qualifying W
  and every partition into parts at least 2 checked, totaling 92,883 cases.
* 347962: r=4, exhaustive n=4 and n=5 (4 and 1,024 colorings), plus
  1,000 sampled colorings at each n=6,7,8. No failure.
* 346167: the deterministic seed-144 order-8 search stopped at the first
  candidate (100 eligible graphs had passed at the last checkpoint).
  Additional 10,000 draws each at orders 9 and 10 produced respectively
  5,945 and 6,369 connected-complement pairs, all passing. No claim of
  exhaustiveness or failure at larger orders is made.

The remaining records quantify over eventual thresholds, infinite objects or
infinite families, or have material source ambiguity. Their exact reasons,
source passages reviewed, and next unresolved steps are in results.json.
No endpoint was manufactured for a parked record.

## Provenance, access and conduct

raw/ preserves every assigned corpus line including its newline. extracted.json
and results.json include one-based line, chunk SHA-256, raw SHA-256 and statement
SHA-256. sources/receipts.jsonl and outputs/source-manifest.json bind downloaded
primary bytes. Complete current registry subtrees and head receipts are retained:
Omega 8a81f0a47894e6d1864fcbc61ba4685a3163b940; OpenAI/math
4eaee87548250b2682affda7d05d947c05554bae. The root recursive responses were
truncated; complete D5, Problems and preprints subtrees were fetched separately.
This is a bounded path screen, not proof-body clearance of every registry item.

The source and accessible companions were checked for ready-made constructions
or source-ingredient bridges. Neither candidate graph has a leaf, is a tree, or
belongs to the standard examples ruled out in TASK.txt. G has 16 edges, so the
K4-minor-free maximum-degree theorem does not immediately provide its bound.
Searches included the exact topic, conjecture number, counterexample language,
theses and 2026 postings. Bounded non-findings do not establish global novelty.
ACCESS.md records unread journal bodies and failed routes.

All work stayed in this lane; no git operations, child agents, browser tabs,
publication, upload, external messages or shared ledger edits. Numerical,
Lean and checker calls used scripts/run with two CPUs, CPU 120 seconds,
wall 140 seconds, sampled aggregate RSS cap 6 GiB and MALLOC_ARENA_MAX=2.
Every Lean call used -M3500. Three development reductions hit Lean's internal
memory cap; splitting certificates into sixteen row modules and simplifying
the literal tables resolved this without raising limits. Full failed logs
remain; no failed development source is in the sanitized archive. Initial
elaboration failures printed automatic sorryAx diagnostics; the final strict
builds, all local axiom audits and both replay endpoints have none.
No background process belonging to this lane is left at handback.

Final validation: archive extraction replay PASS, 20/20 strict modules and
20/20 explicit-module checker calls; all 168 local declarations pass recursive
axiom and metadata audits (no unsafe, partial, implemented-by or extern flags).
All twenty raw and statement hashes were rechecked. See
outputs/final-validation.json. Source-only archive SHA-256:
038c7acfb665189952f706cfdf65de6d9bc5dc16c4a7af70f3b0832ec4c86057.
