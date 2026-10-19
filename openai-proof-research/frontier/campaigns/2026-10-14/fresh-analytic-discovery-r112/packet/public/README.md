# r112 handoff

Bounded pre-freeze analytic/geometric research. No frozen target, full candidate, or nominee. Start with research-report.md; operation-comparison.md gives the concrete reductions, and reading-ledger.md limits their interpretation.

Run, supplying the detached manifest hash communicated outside this packet:

```
python3 -B public/verify.py /absolute/path/to/packet DETACHED_FINALHASH
```

The verifier is offline and read-only. It has no adjacent-hash fallback, performs no repair or reseal, and does not run mathematical tests. Its own bytes are covered by the externally anchored manifest. Trust begins with the external hash and the verifier code/runtime; this is not a signature, timestamp service, or mathematical gate.

`public/` contains original prose and code. Original prose: CC BY 4.0. Original code: MIT. Parent integration may select these originals and original integrity metadata. `private/` contains upstream/third-party bodies and local search evidence under original rights; do not stage or publish those bodies under the original-work licenses. The packet is a local review archive, not a public release.

The manifest excludes only itself; its hash is detached. `final-anchors.json` and copied-control receipts are outside packet. No report hash inside packet serves as an authority. The original status is preserved and bound separately by the verifier. There is no freeze to weaken or repair.
