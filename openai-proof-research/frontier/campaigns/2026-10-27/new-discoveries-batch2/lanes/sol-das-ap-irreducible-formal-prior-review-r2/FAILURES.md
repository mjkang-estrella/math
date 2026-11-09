# Review-local failure

First final verification exited 1, before writing a receipt. It resolved an inherited relative frozen-copy path from the workspace rather than the extracted archive root:

```
verify.py line 14: assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256']
FileNotFoundError: frozen/claude-wide-finite-algebraic-scout-r245/discovery.md
helper guard_exit=1; sampled_peak_group_rss=24752128; wall_seconds=0.08022505999542773
```

Corrected only the review verifier's relative-path resolution; no scientific bytes changed. This is a verifier path failure, not evidence of a mismatched scientific file. The failed invocation also misspelled PYTHONDONTWRITEBYTECODE as PYTHONDONTWRITECODE in its outer shell assignment. No local module was imported and no pycache/pyc appeared; the corrected final run uses the required spelling. Other review Python invocations used the required spelling. Inherited failures remain separately recorded in extracted/FAILURES.md and the immutable original lanes.
