# W020: exact public table encoding and numerical layout

Verdict: **verified limited representation result**, independently reviewed.
Date: 2026-10-07 local / 2026-10-08 UTC. Author: native Astra
`/root/encoding_review`; independent source/proof review and integration:
coordinator Astra. This is a distinct reviewer, not a different model family.

## Claim and boundary

`Research/WordQueryData.lean`, frozen SHA256
`39e285ab85571809121d9160cd2f9fecaf30ffe2d5c7365d841215655b7dcf14`,
implements the amended W016 encoding and numerical layout. Primary local
specification: research/proposals/W016-word-query-contract.md, hash
`3aa67dbd8e98de67878d978cb895f3d3763474546ff4ed5dc39c54ec517b92b5`.

The public sizes determine W,m,k, all heap addresses, R=32, output width2,
setup count and the unchanged unproved challenge budget. Numerical admission
is W>0, k<=W, M<=2^W. It is explicitly **not code admission**. Typed data
contains all m entries with bounded keys and payloads, and every bounded query.
Sortedness is a separate precondition and is never silently imposed by encoding.

The exact raw bit sequence is little-endian W-bit m, W-bit k, m records of
k-bit key/W-bit payload, and the k-bit query. The entire table prefix is query
independent. The exact length is L, rawInput preserves every bit, and the host
suffix parser reconstructs the data without consuming its suffix. Encoding and
raw input are injective on numerically admitted sizes. The proof covers all
entries and queries, not a sampled or narrowed secret domain.

Numerical proofs include header/word/field/address bounds, safe record index
increment and the M=U exclusive-endpoint case. A sorted all-zero data witness
exists for every shape, and k=0 forces every key/query to zero. This witness is
not a proof that either forthcoming code graph is admitted.

## Review and validation

Coordinator read every definition/theorem, checked formulas and field order
against W016, checked the actual WordCore profile fields, and verified that
parser range/header checks are host representation tools rather than claimed
free guest validation. Injectivity follows from typed suffix roundtrips; the
payload remains part of the encoding, including at k=0 and with duplicate keys.
Proofs do not assume sorting or a hidden inverse table. All 28 named public
theorems are added to Audit.lean; none is inferred merely from a test result.

Exact independent commands from dlp-research:

```
timeout 60 ./scripts/lake.sh env lean Research/WordQueryData.lean
./scripts/check.sh > /tmp/ecdlp-w020-check.log 2>&1
sha256sum Research/WordQueryData.lean
```

Both commands exited0. The integrated check passes **303 named theorem audits**
(previous275 plus28), source screening, full build and executable smoke check.
All dependencies are among propext/Classical.choice/Quot.sound. Kernel fixtures
exercise numerical boundary M=U, empty/zero/full-width representations, maximum
values, duplicates with different payloads, suffix preservation and malformed
headers. These tests execute representation tools, not query guest programs.

Author retained three intermediate compile failures: unreduced R/distributivity,
Option-bind unfolding, and Vector list reconstruction. They were corrected
without increasing limits or weakening statements. No algorithm/runtime failure
is hidden. Independent review found no change needed to the frozen file.

## Remaining obligations and parallel checkpoint

No instruction constructor, executed packing, common code-admission witness,
F-sufficiency theorem, query correctness/cost comparison, or EC solver speedup
is established. WordCore/WordRun and Machine/Problem/Goals remain unchanged.
Host parser runtime and source-table production/sorting are excluded; no hardware,
bit complexity, complete BSGS or cryptographic transfer follows from this module.
A counterexample to any claimed exact length/roundtrip/injectivity would falsify
this milestone; a failing query would instead concern the still-open refinement.

Sol froze W018's numbered graphs for separate operational review. They remain
an unaccepted design pending Astra's independent report; no constructors have
been written. W019 archives the recovered Grok literature report and original
Smart prototype as **unaccepted evidence**; Factory Fable's new focused audit is
live. Exact task IDs and status are in research/STATE.md. Keeping these artifacts
in this checkpoint does not endorse their mathematical or runtime assertions.
Next: accept or repair the graphs after review, then instantiate their fixed
skeleton with actual shared admission before proving fresh-run behavior.
