# Round 4A validation

Measured receipts are generated in results.json after fresh replay. Full logs
are retained under logs/ and fresh-extraction/logs/. The source zip excludes
compiled objects; package.py requires a new empty extraction directory.

The frozen formal modules and inherited audit source are recorded in
frozen-before.sha256 and frozen-after.sha256. Failed development diagnostics
are retained in unique logs; only the final source modules are in modules.txt.
The final full-closure audit rejects every prohibited local metadata flag and
transitive axiom, and reports upstream metadata separately.

Finite regression is evidence, not a substitute for the open general erasure
proof. Kernel-decided erasure base cases are separate formal theorems.
