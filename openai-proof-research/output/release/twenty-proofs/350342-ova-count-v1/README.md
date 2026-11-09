# Thirty-eight prime outputs refute the Ova counting bound

MathDB [350342](https://mathdb.com/p/350342). Full proof independently reviewed; release verification records are included.

The source construction has at least 38 distinct prime outputs for inputs 677 and 401; both bounds 10 and 13 are false.

- [Paper source](main.tex), with `paper.pdf` in the release
- [Complete written proof](PROOF.md) and [Lean certificate](formal/OvaCount.lean)
- [Independent review](review.md), [coverage](coverage.json), and [verification](verification.json)
- [Source extract](source.json), [provenance](primary-reference.json), and [prior status](NOVELTY.md)

The extracted release includes `verify_outcome.py`, `build_paper.py`, and dependency pins. From that directory run:

```sh
python3 verify_outcome.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

From this campaign checkout, use `python3 ../../verify_outcome.py .` instead. The verifier compiles an isolated, byte-identical source copy and checks every listed declaration's axioms. The Lean version is 4.34.1; dependencies must already be compiled. Full third-party source bodies and original API snapshots remain in `frontier/campaigns/2026-10-25/next-discovery-lane/sources/`, not in this release; versioned source references and hashes are preserved here.

Independent local formal verification of a known posted result; no new-discovery or first-formalization claim.

See [independent review](review.md) and [verification](verification.json).
