# All-order repeated-integral conjecture

This packet proves Burke–Haris–Madhavendra Conjecture1.2 for every natural
order, including0 (MathDB371768, arXiv2512.02151v1 p2).

Read paper.pdf, proof-map.json, REPRESENTATION-PROOF.md and FINAL-STATUS.md.
The complete literal source theorem is `RepeatedIntegrals.source_conjecture_371768`.
Its129 declarations in18 modules have no residual moment, smoothness, convexity,
openness, kernel or basis hypotheses. General moment tools and the known n≤3
cases are credited and receive no separate discovery credit.

Replay with the pinned compiler and packages:

```
python3 verification/verify_candidate.py . --lean-bin /absolute/path/to/lean --packages /absolute/path/to/.lake/packages
```

The verifier checks Lean4.34.1, every revision in verification/pins.json,
clean dependencies, fresh isolated objects, warnings as errors, declaration
types and axioms. Only propext/Classical.choice/Quot.sound are permitted.

The independent final review is verbatim in reviews/final/. The parent
reconciliation is reviews/parent-final-addendum.md. All42 reviewed bytes are
preserved at the locations in reviewed-file-locations.json; three manuscript/QA
files have final copies as well as the reviewed originals. Mathematical text,
bibliography, all18 Lean modules and verifier are unchanged by final editing.

Retained PROOF.md, provenance.json and component checkpoint metadata describe
earlier approaches or partial states. Their old statuses are historical; the
authoritative present proof is the closed endpoint, the final paper and
FINAL-STATUS.md. No old closed-cone/density argument is load-bearing.

The archive is assembled before final extracted replay and contains preacceptance
credit0 metadata. A later acceptance.json, if present, is outside the immutable
archive and records final extracted replay and discovery credit. The campaign
ledger is authoritative. No absolute priority or new general moment machinery
claim is made; the bounded literature/access limits remain explicit.
