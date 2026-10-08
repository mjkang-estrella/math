# W022: fixed typed query code, common admission and actual serialization

Verdict: **verified structural/admission/serialization milestone**. This does
not establish query correctness, runtime counts or a speed comparison.
Author: native Sol `/root/small_curve`. Independent reviewer: native Astra
`/root/encoding_review`. Coordinator independently inspected the instantiator,
admission/length proof statements, compared all graph rows and integrated.

## Exact code and no-advice boundary

Accepted W018 graph hash remains
`08b5befa350dcd0d7f4b98932cb59a0ba3faca54683e911265af3b185b48cf26`.
Research/WordQueryCode.lean has one symbolic common array and two fixed bodies,
with 86 common instructions and total lengths 110 and 115. Template registers
are Fin32. Literal slots are exactly fixed naturals plus W,L,B,A,A+1,A+2.
A single instantiator preserves every primitive opcode and operand order,
constructing each word from its actual value and bound proof. No reduction,
fallback code, host query, table data or unrolling occurs in the constructors.

`linear` and `binary` take public Sizes and an admission proof only. Their code
fields are definitionally the same instantiation function applied to the fixed
skeletons, satisfying the W016 fixed-graph requirement directly by construction.
The evidence_irrelevant and size_only theorems separately certify proof/public-
size equality. The actual typed arrays share their first 86 instructions.
This array equality is not yet equality of fresh-run prefix traces.

Admission is the intersection of numerical prerequisites and **both actual
array lengths/all immediate and target word bounds**. Register bounds are in
TemplateInstr's type. Its decidable predicate is proved equivalent to numerical
admission and W>=7. Eight W018 shapes are accepted, including nonempty k=W,
zero-width keys, empty tables and M=U. Oversized heaps and W<=6 are rejected.
This supplies nonvacuous actual code admission, not merely numerical witnesses.

The actual WordCodec.programBits theorems give:

- linear: 10205 + W + B + 4*A + L;
- binary: 11082 + W + B + 4*A + L;
- profile descriptor: W + M + L + 39;
- manifest: profile descriptor plus the corresponding actual program length;
- separate unary fuel descriptor: F+1.

The deliberately noncompact codec remains unchanged. These lengths neither
price host descriptor construction/code loading nor prove F sufficient. No
constant description budget or hardware/bit/tape complexity follows.

## Review, commands and failure history

Author froze hash
`05c5283142c27c4463abbce8a5b5e34cd64fd2c6d8ee172fc4024c306e17d2da`.
The integrated lexical screen intentionally flags the standalone word `admit`
even in comments, and stopped at a doc comment near rejected_6_0_0. Coordinator
changed only that comment to say numerical layout does not establish either
code bound; no checker was weakened. Final independently reviewed hash:
`362e4ea41199bcbbaa11f8cb050e416ba757a173fc46c715b1bf3cb060182a82`.
Reviewer confirmed reversing the one comment change reconstructs the original
hash. No theorem or executable instruction changed after author freeze.

Reviewer checked all 139 common/body rows, every instantiation case, all public
proof statements, admission role coverage and symbolic serialization arithmetic.
All 37 named theorem axiom audits passed with only propext/Classical.choice/
Quot.sound dependencies. Coordinator's independent normalized source-row check
also matched all 139 rows; it is a review aid, not a hardened Lean parser.
Artifact research/artifacts/W022-query-graph-match.py has SHA256
`822254861c1dc4bf36c0ad8d320dcc7f156b71013863e9408e85c30265eb08f2`.

Exact commands from dlp-research:

```
timeout 60 ./scripts/lake.sh env lean Research/WordQueryCode.lean
python3 research/artifacts/W022-query-graph-match.py
./scripts/check.sh > /tmp/ecdlp-w022-check.log 2>&1
```

Independent standalone compile passed. Graph match printed rows_matched139/PASS.
Integrated check passed **347 named theorem audits** (310+37), source screen,
full build and executable smoke output. Every new named theorem is in Audit.lean.
No actual query guest has been run by this milestone's validation.

Author retained intermediate failures: missing explicit power-base inference,
unsupported by_contra, residual function-unfolding goal, broad simp heartbeat
exhaustion and nonexistent Array.toList_mk. Narrowed rewriting/simplification
resolved them without increasing limits or weakening the target formulas.

## Next operational refinement

W016's remaining conditions are binding: actual raw prefix contents and state-
based trace split; no faults/input writes; deterministic IndexedLookup match
and first sequential match; all-input halting within common F; actual opcode/
search/total ledgers and reviewed per-input comparisons. No event contains PC.
Whole BSGS costs, streaming/lazy alternatives and ECDLP transfer remain open.

Next disjoint work: Sol owns WordQueryDecoder.lean for actual operational field
loop refinement; Astra owns WordQueryInputFacts.lean for raw-input field-bit
association. Coordinator owns independent fresh-run tests and integration.
These are new proof obligations, not retroactive claims about these constructors.
