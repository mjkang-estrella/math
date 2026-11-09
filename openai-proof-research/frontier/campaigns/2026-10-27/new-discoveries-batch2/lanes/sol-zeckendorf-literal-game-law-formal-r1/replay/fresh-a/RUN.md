Run from this lane, with the fixed guard G at ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py.
Every invocation uses OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1.

Development:
1. python G python runner.py -o Literal.olean Literal.lean
2. python G python runner.py Inventory.lean
3. python G python package.py audit
4. python G python runner.py Audit.lean
5. python G python package.py pack

Fresh replay: python G python replay.py (requires replay/fresh-a and fresh-b absent).
Final independent verification: python G python verify.py.

All helpers retain AS/group RSS 512MiB, CPU210s, wall230s. Only runner.py's
Lean child uses the expressly authorized serial exception: -j1 -M2700,
group RSS2800MiB, CPU210s, wall230s, warningAsError=true, autoImplicit=false.
No package is rebuilt or edited. All nine package HEAD revisions are read and
compared with the saved manifest before and after extracted replay. The pinned
compiler's SHA256 is checked before each compile. Attempts are append-only.

This is an incomplete component, not SourceClaim or a normalized stochastic law.
