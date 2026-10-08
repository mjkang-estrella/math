# H032 explicit memory–recovery cards

LATEST DISPOSITION: the stated R1 SINGLE-BATCH HARD-PEAK capacity rationale is
falsified by retaining its own construction descriptors. Independent critic and
original proposer agree; see H032-retrieval-capacity-falsifier.md. A possible
lookup-cost tradeoff is separate and has no supported full-work gain. Historical
proposal/review below is retained, not silently rewritten as a discovery.

Status: UNVERIFIED independent native Sol proposals; no supported complete-work
gain or experiment-ready survivor. Proposer `/root/h010_early_dependencies`
COMPLETED initial ideation without reading the other H032 proposals. No edits,
experiments/imports, children or commits. This summary preserves three genuinely
different mechanisms; completed independent review is recorded below. Root alone integrates.

## R1: frozen endpoint-to-seed retrieval without stored coordinates

Keep the competent existing negation-aware walk, its cycle policy and jump table.
Starts come from a domain-separated counter generator. Seed replay reproduces
points, orientations and affine labels. Predetermine trail/start/build/query caps.
Collect a finite batch of w DP endpoints. Retain each endpoint's three hash-cell
indices, seed counter and tag, not its full coordinates. Sort compact descriptors
in place. Repeated signatures cause paid seed replay and exact endpoint comparison:
recover useful collisions immediately; deduplicate redundant endpoints; unequal
endpoints with equal signatures force a new paid hash/build attempt.

Peel a three-cell XOR retrieval graph mapping genuine endpoints to(seed,tag).
Explicitly fail when construction cannot finish within cap. After building,
discard descriptors. A subsequent DP query retrieves a payload; a tag pass causes
seed replay and exact endpoint equality check before any scalar recovery. Verify
the recovered scalar against Q and dispatch O. Nonmember retrieval may return
arbitrary data; tags are probabilistic filters, not equality proofs.

Known antecedent, not claimed invention: proposer read Dietzfelbinger–Pagh
§§1.1–1.3,2.2 [primary paper](https://www.rasmuspagh.net/papers/bloomier.pdf).
It does not make construction scratch, concrete hash evaluation or retries free.

Literal hard-peak reservation from the proposer, independently checked below:
u=ceil(log2(w+1)), v=ceil(log2(m+1)), seed width s, tag width t, degree width d.

    E = w(3v+s+t)         incidence descriptors
    V = m(d+u)           vertex bookkeeping
    Q = mv               queue
    P = w(u+v)           peel stack
    peak includes E+P+max(V+Q, m(s+t)).

The max assumes vertex/queue storage is freed before result back-substitution.
Add live walkers, jump tables, replay/hash/sort state and every other retained
batch. The array m(s+t) alone is NOT the construction peak. Every failed peel,
rehash, descriptor collision and unsuccessful replay remains paid. Hard caps
require an explicit failure/restart/fallback contract.

Possible source of gain: more retained endpoints under binding peak memory might
reduce DP delay. It does not create new geometric collision opportunities.
Bootstrap/delayed detection, static freezing versus ongoing insertion, hash
behavior and rebuilding may erase any benefit. No calibrated costs or favorable
parameter regime supplied. Cheapest falsifier: compare complete construction
peak and stopped work against packed seed-replay DP storage, optimizing density
in both arms and including failure. No standalone retrieval benchmark admitted.

## R2: overloaded invertible sketch witnesses

Fixed cells store counts, key sums, seed sums and checksums. Query before inserting
an endpoint; an isolated matching cell may recover a previous seed. Replay and
exact equality are mandatory. Ambiguous cells require paid peeling or fallback.
Repeated keys with different seeds need multiple-value handling.

Proposer read Goodrich–Mitzenmacher §§2.3–2.4,3
[primary paper](https://arxiv.org/pdf/1101.2245). Fixed allocation during overload
is not a guarantee of successful lookup/listing. In an ideal hash model clean-cell
probability has decay involving exp(−kw/m); actual useful-witness detection needs
its own law. More represented records must outweigh lost detection, larger cells,
hashing, peeling, replay and failures. No surviving cost premise was supplied.
Disposition: scoped failure of this proposed overloaded recovery contract, not a
universal sketch impossibility. No run.

## R3: punctured scalar-label completion

Store reduced coefficients a_bar,b_bar for endpoint P=aG+bQ, omitting c high bits
of each. On a genuine match reconstruct via

    P−a_bar G−b_bar Q = u[H]G+v[H]Q, 0≤u,v<2^c.

This is paid meet-in-the-middle completion over omitted metadata, NOT narrowed
secret input or an inverse oracle. Generate one side into a dictionary and scan
the other. Handle all valid completions and require a nonzero scalar coefficient;
verify any recovered discrete log. Saving2c bits per endpoint introduces order2^c
point generation and temporary records per completion, plus basis construction
and normalization. Large savings are expensive; small ones lack a demonstrated
advantage over compact seed replay. No uniqueness or useful-denominator guarantee.
No current favorable regime or prior-art distinction found, no run admitted.

## Review gate

R1 is a paper-only possibility, not accepted improvement. Mandatory comparator
includes H030 hierarchy, known packed/replay DP and H019 where memory permits.
Review must distinguish the actual endpoint distribution from uniform hash
assumptions, final space from peak scratch, membership from reconstruction, and
first-useful-collision stopping from isolated map throughput. All failed builds,
discarded trials and target-independent preprocessing count for one target.
Verified improvement NONE; square-root reference unchanged.

## Independent review completed

Native Astra `/root/h007_additive_relations` separately reviews R1 after the
initial proposals completed. Its exact gate, checked by root:

    peak = w(4v+u+s+t) + m max(d+u+v,s+t)

before all other solver storage. A successful literal peeling construction needs
m≥w because each edge receives a distinct pivot vertex. Rehashing descriptors
without endpoint coordinates requires replaying each retained seed to reconstruct
the endpoint and recompute its new indices; it is not merely O(w) cheap hash work.
Final review COMPLETED, no favorable regime or experiment admitted. The
comparison must optimize both arms' density under the SAME hard peak and count
all generated/replayed group operations plus construction/query/recovery work
through actual first verified success, including failed attempts. Frozen archives
and delayed construction do not inherit the continuous-insertion DP stopping law.

For tags, suitable independent fixed-query models can yield filtering bounds,
but arbitrary payloads and adaptive/repeated queries do not automatically have
independent2^{-t} errors. Returned seeds need range checks and bounded replay.
Exact endpoint/scalar verification protects correctness, not an assumed small
false-hit cost. Pairwise-universal hashes alone do not justify every composition.

Next gate: freeze one complete archive/rebuild/replay contract and derive its
peak-memory and stopped-work comparison on paper. No hardware price, isolated
retrieval benchmark or numeric pilot repairs a missing stopping model. This is
not a universal rejection of static retrieval. Validation: ./scripts/check.sh >
/tmp/ecdlp-h032-proposals-check.log 2>&1 exit0,366 existing audits. No Lean change.
