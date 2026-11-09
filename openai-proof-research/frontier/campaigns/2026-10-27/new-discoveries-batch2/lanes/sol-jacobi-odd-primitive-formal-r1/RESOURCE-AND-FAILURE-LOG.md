# Resources and corrected development failures

Every formal attempt used the copied guard and root runner: sequential `-j1`,
`-M4096`, warnings as errors, no implicit variables, sampled 3 GiB aggregate
runner/Lean RSS guard, no virtual-memory cap. The complete actual logs and JSON
receipts are retained; `verification/development-index.json` indexes all of them.
No formal process was killed by the guard. No optional numerical diagnostic
was run, and no library was rebuilt or upgraded.

The initial rational algebra adaptation needed a polynomial constant cast
simplification and an evaluation-at-zero rewrite. An attempted dependent build
before that module had passed reported its missing import; it is retained.
The triangular module then required explicit rational/natural denominator casts,
subtraction normalization, and removal of unused simp arguments. A top-coefficient
rewrite was made specific to the successor coefficient instead of matching the
leading coefficient. The linear-combination tactic import was added.
The primitive module required projecting pair coordinates before distributing
ring homomorphisms, the current `eval_finsetSum` name (the deprecated alias was
rejected as an error), the coefficient/evaluation-zero identity, and directed
constant-map simplification. A trial reverse `C_pow` simp rule looped; that
failed attempt is retained and the final proof uses only directed map identities.
All these errors were corrected in the final sources. No failed elaboration or
self-axiom diagnostic was used as a certificate.

Exploratory read-only searches also encountered a missing root-level guard path
(the supplied guard lives in `formal/`) and incorrect relative library paths;
the corrected exact files were read. No conclusion relied on those failures.

## Development attempts

| Attempt | Module | Exit | Sampled RSS KiB | Guard killed |
|---|---|---:|---:|---|
| 001-BinaryDigits.log | BinaryDigits.lean | 0 | 1895556 | False |
| 002-Filtration.log | Filtration.lean | 0 | 2087172 | False |
| 003-Riccati.log | Riccati.lean | 0 | 2085224 | False |
| 004-NonSubring.log | NonSubring.lean | 0 | 2069052 | False |
| 005-MidpointAlgebra.log | MidpointAlgebra.lean | 0 | 2246004 | False |
| 006-MidpointSequence.log | MidpointSequence.lean | 0 | 2253500 | False |
| 007-MidpointParity.log | MidpointParity.lean | 0 | 2285572 | False |
| 008-MidpointNormalForm.log | MidpointNormalForm.lean | 0 | 2282364 | False |
| 009-MidpointRational.log | MidpointRational.lean | 1 | 2290312 | False |
| 010-OddTriangular.log | OddTriangular.lean | 1 | 188 | False |
| 011-MidpointRational.log | MidpointRational.lean | 0 | 2288612 | False |
| 012-OddTriangular.log | OddTriangular.lean | 1 | 2283944 | False |
| 013-OddTriangular.log | OddTriangular.lean | 1 | 2294964 | False |
| 014-OddTriangular.log | OddTriangular.lean | 0 | 2298192 | False |
| 015-MidpointPrimitive.log | MidpointPrimitive.lean | 1 | 2299308 | False |
| 016-MidpointPrimitive.log | MidpointPrimitive.lean | 1 | 2294804 | False |
| 017-MidpointPrimitive.log | MidpointPrimitive.lean | 1 | 2291548 | False |
| 018-MidpointPrimitive.log | MidpointPrimitive.lean | 0 | 2291496 | False |
| 019-OddPrimitiveSequence.log | OddPrimitiveSequence.lean | 0 | 2256852 | False |
| 020-OddPrimitiveInventory.log | OddPrimitiveInventory.lean | 0 | 2745088 | False |
| 021-OddTriangular.log | OddTriangular.lean | 0 | 2294964 | False |
| 022-MidpointPrimitive.log | MidpointPrimitive.lean | 0 | 2289188 | False |
| 023-OddPrimitiveSequence.log | OddPrimitiveSequence.lean | 0 | 2265284 | False |
| 024-OddPrimitiveInventory.log | OddPrimitiveInventory.lean | 0 | 2745044 | False |
| 025-OddPrimitiveAudit.log | OddPrimitiveAudit.lean | 0 | 2265052 | False |

## Fresh extracted replay

The independently extracted, source-only replay passed every proof and audit.
It began with zero local oleans, used only the pinned upstream package libraries,
and finished with identical packaged source hashes. Its complete receipt is
`verification/fresh/receipt.json`; its module runner and Lean logs are adjacent.

| Module | Exit | Sampled RSS KiB | Seconds |
|---|---:|---:|---:|
| BinaryDigits | 0 | 1891000 | 1.003 |
| Filtration | 0 | 2087232 | 1.403 |
| Riccati | 0 | 2085572 | 1.403 |
| NonSubring | 0 | 2058108 | 1.002 |
| MidpointAlgebra | 0 | 2249520 | 2.204 |
| MidpointSequence | 0 | 2253632 | 1.204 |
| MidpointParity | 0 | 2275004 | 2.003 |
| MidpointNormalForm | 0 | 2282748 | 1.403 |
| MidpointRational | 0 | 2290112 | 2.406 |
| OddTriangular | 0 | 2287736 | 1.604 |
| MidpointPrimitive | 0 | 2289196 | 2.004 |
| OddPrimitiveSequence | 0 | 2261128 | 1.204 |
| OddPrimitiveAudit | 0 | 2268348 | 1.205 |
| MidpointAudit | 0 | 2264764 | 1.203 |
| FiltrationAudit | 0 | 2050788 | 1.203 |
| OddPrimitiveInventory | 0 | 2745208 | 9.214 |

Fresh sampled peak: **2,745,208 KiB**, below **3,145,728 KiB**.
