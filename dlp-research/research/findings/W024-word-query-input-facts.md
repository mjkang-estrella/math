# W024: actual raw-input field-bit associations

Verdict: independent coordinator review **PASS**, limited representation result.
Author native Astra `/root/encoding_review`; reviewer coordinator Astra.
Frozen Research/WordQueryInputFacts.lean SHA256:
`a1fbcc6156c0ce88790001f33e66c7ffc9abae02f9c138fff5f1ba3d97fdff12`.

The six bounds and ten bit/value association theorems connect actual rawInput
to both header fields, each key/payload and the query. Offsets are exactly
0, W, recordStart(j), recordStart(j)+k and queryStart. For every valid field
index i, the actual Boolean source value equals bitValue(field,i)==1 and its
0/1 natural conversion equals bitValue(field,i). No replacement bit buffer or
packed-state assumption is introduced. Proofs use the actual nested concatenation
and vector/list entry correspondence, then WordPacking.bits_getElem.

These statements need no admission: indices are natural bit-list positions,
not yet guest words. Outside admitted sizes, header bits can truncate m/k;
full header recovery still needs the separate proved numerical header bounds.
Zero-width fields have no valid bit index, as intended; zero-width/full-width
and empty-table layouts need no special unproved branch. Every present payload
retains its own entry association even with duplicate keys.

Coordinator read all definitions/proof statements and private indexing helpers,
checked every field width/offset against W016 and the actual encoder, and ran:

```
timeout 60 ./scripts/lake.sh env lean Research/WordQueryInputFacts.lean
```

Clean exit0. Author's separate 16 axiom audits used only propext and Quot.sound.
Coordinator adds all16 named claims to Audit.lean and imports the module before
running the integrated check. One author intermediate compile failed because
an omitted explicit hi left five index-proof goals; supplying the existing hi
resolved them. A redundant simpa warning was removed. No weaker statement,
new assumption, resource-limit increase or runtime counterexample was hidden.

No guest load, decoder state transition, field-loop count, fresh-run correctness,
fuel sufficiency or ECDLP result is claimed. This is the source-side bridge to
Sol's separately owned actual WordQueryDecoder operational proofs. The intended
use combines these identities with WordRun.initialized_input and preserved heap
invariants; that connection is still an operational obligation.

Integrated verification: `./scripts/check.sh > /tmp/ecdlp-w024-check.log 2>&1`
exited0 with363 named theorem audits (347+16), source screen, full build and
smoke output. All dependencies remain within the standard allowlist.
