# Runtime and access notes

All Python script invocations used `python3 -I -B` with real script paths. No packages were installed, downloaded code executed, or source archives extracted. The only extraction was the lane's own Lean packet into a fresh lane-local directory. No `__pycache__` or `.pyc` was found in the lane at final inspection.

HTTP receipts use exclusive existence checks and unique names. Direct requests to inherited denied services were blocked by the fetch script. Redirects to denied hosts are refused. No TLS bypass was used. The initial www.math.ucsd.edu PDF request failed certificate validation; the distinct official fanchung.ucsd.edu author host succeeded. One guessed thesis path returned 404; it was not retried. One unrelated arXiv ID guessed during search was retained as an explicitly irrelevant receipt.

The imported resource wrapper caps CPU 120 seconds, wall 140 seconds, two allowed CPUs and address space 12 GiB, with a sampled 6 GiB RSS stop. Numerical loops are capped through it. The original `run_lean.py` spawned Lean under a Python process, so its sampled parent RSS undercounts the Lean child; the final `lean_exec.py` uses exec and gives direct Lean RSS near 1.9 GiB. All Lean compile calls use -M3500. Failed first thread allocation led to -j1 for all final calls.

`leanchecker --help` is not a help command. It unexpectedly began default-module inspection, and was interrupted after the tool returned a running session. This discovery call was not under the wrapper and is a procedural deviation. The explicit final `leanchecker Hurlbert` call is capped and passes. It is an internal Lean replay, not an independent external verifier.

An optional C++ enumeration was not run because g++ is absent. The Python replacement enumerated the first 100000 lexicographic S4 tours. An initial extracted auxiliary-name audit failed on a linter; both its archive/logs and the corrected successful v2 packet are preserved. The proof source itself remained strict without linter suppression. Only the audit's references to generated declaration names need `linter.auxLemma false`.

The lane did not intentionally mutate shared files, use git, launch child agents, send external messages, publish, open browser tabs, or leave jobs running. Network/metadata calls and inexpensive text conversions were not treated as heavy numerical searches.
