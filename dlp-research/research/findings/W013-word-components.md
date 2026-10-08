# W013: internal word steps and actual program serialization

Date: 2026-10-07. Status: independently verified limited component result; core and codec PASS.
This is a verified-component milestone under the independently amended W011
contract, not an ECDLP improvement or a complete word-machine cost theorem.

## Claim and falsification target

Hypothesis: W011's thirteen checked-word operations and actual unary-prefix
serialization admit executable Lean definitions with fault atomicity, genuine
fetch/opcode events, typed bounds, suffix roundtrips and exact encoded lengths.
Falsifiers include a mismatched operand order, reading a mutated source during
aliasing, checking a successor before its next fetch, labeling an event with an
unexecuted operation, truncating out-of-range operands, ambiguous serialization,
or claiming a size unrelated to the actual bit list.

The comparison baseline is the rejected W010 cost design, not an attack runtime.
Frozen Machine/Problem/Goals and existing BSGS count theorems are unchanged.
No new primary-literature claim is made: the source is the reviewed W011
operational contract and its explicit amendments (see W011-contract-review.md).

## Executable internal steps

Native Sol `/root/small_curve` authored only Research/WordCore.lean. Profile fixes
positive W/R and heap/layout bounds. Instructions have typed word/register
operands; programs bound their actual array length. States contain actual
register/heap vectors and PC. execInstr reads pre-state operands, returns
continued/halted/faulted, and guards arithmetic and addresses. step fetches
actual code and derives either an invalid-PC event or the fetched opcode and
its actual disposition. Targets outside code remain legal words until fetched.

Twelve generic lemmas include fault atomicity, actual fetch/event correspondence,
word bounds, characterization of halt/invalid-PC, and shared-destination divmod.
Eleven kernel-reduced boundary theorems cover all thirteen opcodes, including
aliases, W=1, M=0, M=2^W, arithmetic bounds, empty code, arithmetic fault before
an invalid successor and committed store before a later invalid fetch.

Independent native Astra `/root/encoding_review` reviewed the frozen source
SHA-256 `a7f0d76b73f5e5254b9571b0e3050cb8d3dca291379a4437f2916f17fb4522a7`.
Verdict PASS, no blockers; all 23 public theorem axioms independently audited,
only propext/Quot.sound. Review command:
`timeout 60 ./scripts/lake.sh env lean Research/WordCore.lean`; additional
`lean --stdin` recompilation appended all 23 axiom reports. No reviewer failure.
Author's one intermediate compile failed on proof-case completion, private
numeral instances and a singleton-size goal with a free instruction variable;
all corrected before freeze. No source escape or new assumed axiom was used.

## Actual codec and size

Coordinator authored only Research/WordCodec.lean, frozen for independent Sol
review at SHA-256
`eead4918922436ddf4acefc86f2e21b0ffd95998e1692fb1027478c1dc29b2be`.
Unary naturals, little-endian four-bit tags and exact operand order implement
section 6. Executable admission checks reject bad tags, arity, register/word
bounds, excessive code count and invalid profiles. Code targets are checked
against word capacity, not code length, preserving deferred-fetch semantics.

Suffix roundtrips cover unary fields, fixed bits, every typed instruction,
instruction lists, programs, profiles and dependent profile/program manifests.
They yield injectivity; lengths are proved for the actual bit lists. Specifically
programBits = (N+1) + sum_i (4 + sum_f (fieldValue+1)). Profiles encode W,R,M,L,O
with length W+R+M+L+O+5; manifests concatenate profile and program. No fixed
program-size budget is asserted, and unary encoding is deliberately noncompact.
Twenty-nine public theorems include reserved-tag rejection and kernel checks
for malformed/out-of-range operands, invalid profiles, empty code and truncated
records. A redundant constructed-array-size admission guard is explicit; the
roundtrip proof shows it accepts every already admitted program.

Development failures preserved: prefix induction initially failed on monadic
simplification and an unreduced empty append; modulo-one needed an explicit
lemma; free-variable decide needed tag reduction; list-length arithmetic needed
normalization; a missing expected Program type prevented dependent pair
elaboration. These were corrected using ordinary proofs. Commands:
`./scripts/lake.sh build Research.WordCore`;
`timeout 60 ./scripts/lake.sh env lean Research/WordCodec.lean` (final exit 0).

## Integration evidence and limits

Coordinator imported both modules in Research.lean and included every one of
these 52 public theorems in Audit.lean. `./scripts/check.sh` passed: source
screen 22 files, full build and demo, **211 theorem dependency audits**, only
permitted propext/Classical.choice/Quot.sound. `git diff --check` passed.
Independent codec review also PASSed; its separate evidence follows.

The core is conditional on an existing guest state. No cost claim may start
there. No initialization, raw-input runner, shared fuel, trace-derived aggregate
ledger or output/solver refinement is integrated in this milestone. Code
loading/decoding and production of source input remain unpriced by contract.
Host bit arithmetic, memory latency, metadata/storage and arbitrary word-width
growth remain outside a hardware/tape/family claim. No linear/binary query
comparison is authorized until W011 section 10's separate gates are reviewed.

## Next distinct step

Independent codec review, then a local coherent commit with accepted contract,
review history and component limits. Native Astra owns only Research/WordRun.lean
for the next wave: partial initialization, raw input, normalized setup/guest
boundary, shared fuel and actual-event trace ledger. It must receive separate
independent review; unintegrated work cannot be counted in this milestone.

## Completed independent codec review

Native Sol `/root/small_curve` independently PASSed the unchanged frozen codec,
no blockers. Commands: `timeout 60 ./scripts/lake.sh env lean Research/WordCodec.lean`
and `./scripts/lake.sh env lean --stdin` with all 29 axiom reports plus separate
adversarial proofs (each command bounded to 60 seconds). Only permitted
propext/Classical.choice/Quot.sound dependencies. No review checks failed.

Reviewer additionally reports successful kernel checks for all 13 manual tags
and asymmetric operand orders, 41 single-position register/word rejections,
wrong direct arities, short tags and truncated final unary operands; N=U
accepted/N=U+1 rejected; representable successors outside code accepted; empty
and full heaps; and arbitrary suffix preservation. A manual 13-instruction
example gave program/profile/manifest lengths 318/26/344 bits. These supplemental
stdin cases were not retained as files, so they are reviewer evidence, distinct
from the 29 audited source theorems and archived boundary proofs. No writes or
source changes occurred. Suffix parsing intentionally does not validate that a
whole buffer has no trailing bits; that would need a separate suffix-empty test.

Both independent reviews approve only their component scopes. Proceed to a
local component/contract/process commit; WordRun remains outside this commit.
