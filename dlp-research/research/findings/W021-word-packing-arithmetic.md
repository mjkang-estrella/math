# W021: descending decoder arithmetic support

Verdict: **verified limited arithmetic result**, independent review PASS.
Author coordinator Astra; reviewer native Astra `/root/encoding_review`, separate
agent. Frozen Research/WordPacking.lean SHA256
`1ad38262382ee58ace6270b1beaaaf1c112ea3587eb96dbc39b8168be5f21e92`.

Purpose: support the forthcoming actual W018 descending decoder proof, without
replacing its instruction execution by a host decoder. bitValue(value,i) is the
actual little-endian bit value value/2^i mod2. `bits_getElem` proves correspondence
to the existing public Research.bits function, at every valid index.

The seven named claims prove bit bounds/Bool conversion, zero initial quotient,
final quotient, the exact Horner identity
`2*(value/2^(remaining+1)) + bitValue value remaining = value/2^remaining`,
and that both the intermediate checked multiplication and following addition
remain below2^W when value<2^W. They do not require remaining<=W; the stronger
arithmetic result is valid even at W0. Future operational proofs must establish
the actual accumulator, cursor, field-offset and heap-bit invariants separately.

Author's first compile passed, with no failed proof attempt. Reviewer read all
statements/proofs, checked actual encoding linkage and edge conditions, then ran:

```
timeout 60 ./scripts/lake.sh env lean Research/WordPacking.lean
```

Reviewer also audited all seven theorems via source-plus-stdin; only standard
propext/Classical.choice/Quot.sound dependencies. No edits were requested.
Coordinator adds all seven to Audit.lean and the module to Research.lean.
Integrated ./scripts/check.sh passed310 named theorem audits, source screening,
full build and smoke output. The first integration check stopped on the separate
new WordQueryCode comment containing the screened word `admit`; coordinator
rephrased only that comment, kept the screen unchanged and reran successfully.
No proof escape was present and no logical statement was weakened.

No decoder program, guest state transition, event count, F bound, query result,
hardware cost or ECDLP improvement is established by these arithmetic lemmas.
The relevant formal specification remains amended W016/exact accepted W018.
Next: use the lemmas in actual raw-run prefix refinement after code acceptance.
