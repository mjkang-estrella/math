# Reproduction and status

This is a diagnostic HOLD packet, not a completed Lean proof packet. Extract only into a new empty directory inside this assigned lane. No network or predecessor file is needed for the exact-arithmetic replay.

Run `python3 -I replay.py --exact-only` from that extraction. It reconstructs all matrices with Fraction arithmetic, checks equations, computes the two pair-sum conventions and spectral traces, checks physical compatibility, and rejects perturbed certificates. It writes outputs/exact-independent.json inside the extraction. The only dependency is Python 3's standard library. No cache is created by Python -I.

`python3 -I replay.py` deliberately exits 3, even with LEAN_BIN and LEAN_PACKAGES supplied, because no Lean endpoint exists. The variables are recognized, not a claim that Lean was replayed. It refuses any existing .olean in the packet tree. It never invokes Lean or leanchecker and cannot report a false formal success. The pinned intended toolchain is Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

No Lean calls occurred, so there is no unaudited invocation without an RSS watchdog. No heavy process was launched. A future actual formal driver must implement the mandated per-call CPU/wall/RSS watchdog before invoking Lean; this diagnostic driver is not that formal driver.

Original predecessor input paths and hashes are in input-hashes-before.json. input-hashes-after.json verifies both original hashes and copied byte identity. scripts/finish_gate.py records those external bindings and is an investigator helper, not the portable replay entry point. scripts/fetch_sources.py is a one-shot receipt-producing network helper and should not be replayed to retry denied routes. The ZIP excludes PDFs, compiled artifacts and fresh-extraction products.

receipts/extracted-diagnostic-replay.json records only diagnostic arithmetic success and expected refusal of formal mode. receipts/audit-status.json records checks NOT RUN. logs/exact.log and logs/extracted-exact.log retain arithmetic output. outputs/negative-controls.json lists exact controls: changing M_00 by one invalidates LML=L; group inverse fails Penrose symmetry and MP fails commutation for nonzero alpha. Alpha=0 correctly does not separate the two inverses. None is a Lean negative control.
