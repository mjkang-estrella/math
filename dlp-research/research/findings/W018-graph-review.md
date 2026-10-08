# W018: independent numbered-graph review

Verdict: **PASS for implementation of the exact frozen graphs only**.
Author: native Sol `/root/small_curve`. Independent reviewer: native Astra
`/root/encoding_review`. Coordinator separately inspected the source tables and
review script, reproduced its results, and accepts this design gate. No claim
of generic executable correctness, actual cost, or speed follows from the gate.

Frozen proposal hash:
`08b5befa350dcd0d7f4b98932cb59a0ba3faca54683e911265af3b185b48cf26`.
The proposal remains unchanged to preserve that hash. Its header's pending
status describes the frozen pre-review artifact; this disposition supersedes
that status only for implementing its exact rows. Material changes reopen review.

## Checks and falsification

Reviewer manually checked every edge, zero/nonzero branch polarity, source-before-
write alias, decoder r27/r11 preservation, zero/full-width paths, index and heap
bounds, cached payload address, source/output separation, code lengths and
literal slots. Common prefix is0..85; entry86; linear110/binary115 instructions.
The proposed W>=7 common admission and eight concrete witnesses passed static
checks. This remains a design fact pending actual typed admission theorems.

Independent Python reference execution parses the Markdown itself; it does not
hand-transcribe the program. It checks the entire claimed prefix register/heap
state, opcode counts, common traces, output relation, first linear match and
binary midpoint algorithm, probe/path counts, source preservation and coarse F
bound. Overflow, unsafe subtraction, out-of-range addresses, wrong output or
count discrepancies would fail explicit assertions. It models positive-fuel
instruction attempts and setup writes. It does not prove the model refines Lean.
Its no-fault assertions are evidence only for the executed cases.

329 paired datasets, 676 calls, 664 halts, 666 prefix checks and **234637** setup
plus guest model events passed. Complete bounded data domains were (W,m,k)=
(7,0,0), (7,0,7) and (7,1,0). Other maximum-value, duplicate, absence, full-width,
maximum-m and M=U cases were targeted, not exhaustive. Eight admitted and three
rejected witnesses plus3120 bounded numerical/admission equivalence triples
passed. Empty-table fuel boundaries and terminal stability passed.

## Durable reproduction

Reviewer initially used stdin, then retained identical temporary source/results.
Coordinator read the script and archived it unchanged:

- research/artifacts/W018-graph-review.py, SHA256
  `d285557a04af7f5df278c3096a69c3a3fa00d153d468ce907647abf76dd856b4`.
- research/findings/W018-graph-review-results.json, SHA256
  `8bc5db98f8d20739952b9f8aec44d22918515d3e69bfb9f7630084bd0be48453`.

Exact coordinator commands from dlp-research:

```
timeout 60 python3 research/artifacts/W018-graph-review.py > /tmp/ecdlp-w018-root-results.json
cmp /tmp/ecdlp-w018-root-results.json /tmp/W018_graph_review_results.json
```

Both exited0; results match the reviewer byte for byte. The artifact also writes
/tmp/W018_graph_review_results.json. Two reviewer runs and one coordinator run
used703911 total model events, below the1M wave limit. No failed execution case
was reported. The earlier manual row68/69 correction is retained in the proposal.

Coordinator independently summed the existing WordCodec unary field lengths
from the Markdown rows: proposed programBits are10205+W+B+4*A+L (linear) and
11082+W+B+4*A+L (binary). These are **formal proof targets**, not yet theorems
about any constructed program. All registers, literals, targets, tags and the
unary instruction count are included; descriptor/fuel bits are separate.

## Outstanding gates and ownership

Sol now owns only Research/WordQueryCode.lean: exact fixed skeleton, size-only
instantiation, actual common code admission/equivalence/witnesses, prefix equality,
and actual serialization length proofs. No query-data parameter, runtime table,
clamping, failed-admission fallback or size-dependent unrolling may appear.
Coordinator alone imports/audits/stages/commits after independent source review.

Generic fresh-run packing/state split, deterministic IndexedLookup refinement,
linear first-match proof, all-input halting/F sufficiency, actual trace counts,
comparison review and every ECDLP transfer remain open. Full packing is the
prescribed comparison policy, not a preprocessing lower bound. Earlier W016
binding conditions remain in force; this review relaxes none of them.
