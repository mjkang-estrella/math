# Collection integrity checkpoint — 29 accepted outcomes

All 29 accepted archives pass the current read-only integrity audit. This is
an artifact/evidence coverage check, not a fresh compilation or a new mathematical
or novelty review. One further qualifying outcome is still required.

For every entry the audit verifies the archive SHA-256 against the ledger, all
payload hashes, exact canonical-file agreement, valid PDF signature, retained
primary-source and independent-review evidence, all module source hashes and
complete declaration/axiom inventories, and a retained extracted strict replay
whose entire payload matches the accepted archive and whose module logs are empty.
No prebuilt proof object is treated as proof of source correctness. The retained
source/novelty reviews and their candid limits govern each mathematical outcome.

Historical independent receipts for outcomes4–7 differ in prose/dependency-path
metadata and (for6–7) the list of headline theorems. Their actual source hashes,
compiler, full compiled declaration/axiom inventories and counts agree exactly.
The complete inventory includes all parent endpoint names; the audit records
these harmless metadata differences rather than claiming byte identity there.

| Outcome | Declarations | Modules | Archive payload files | Integrity/evidence |
|---:|---:|---:|---:|---|
| 1 | 67 | 7 | 24 | PASS |
| 2 | 37 | 6 | 22 | PASS |
| 3 | 55 | 7 | 28 | PASS |
| 4 | 50 | 6 | 24 | PASS |
| 5 | 53 | 7 | 26 | PASS |
| 6 | 48 | 3 | 21 | PASS |
| 7 | 78 | 10 | 33 | PASS |
| 8 | 34 | 5 | 25 | PASS |
| 9 | 37 | 6 | 28 | PASS |
| 10 | 36 | 3 | 24 | PASS |
| 11 | 36 | 2 | 25 | PASS |
| 12 | 76 | 12 | 33 | PASS |
| 13 | 61 | 3 | 31 | PASS |
| 14 | 53 | 6 | 30 | PASS |
| 15 | 211 | 17 | 45 | PASS |
| 16 | 136 | 8 | 48 | PASS |
| 17 | 41 | 7 | 49 | PASS |
| 18 | 47 | 7 | 79 | PASS |
| 19 | 129 | 18 | 69 | PASS |
| 20 | 100 | 19 | 77 | PASS |
| 21 | 49 | 12 | 55 | PASS |
| 22 | 117 | 16 | 98 | PASS |
| 23 | 26 | 5 | 75 | PASS |
| 24 | 64 | 11 | 72 | PASS |
| 25 | 21 | 3 | 65 | PASS |
| 26 | 162 | 17 | 122 | PASS |
| 27 | 121 | 19 | 77 | PASS |
| 28 | 49 | 5 | 41 | PASS |
| 29 | 28 | 4 | 39 | PASS |

Reproduce with `python3 verification/audit_collection.py`. The machine-readable
report binds the current ledger hash and records every packet, endpoint, receipt,
review path and matching extracted replay. It must be rerun after outcome30 is
accepted; this checkpoint does not assert goal completion or worldwide priority.
