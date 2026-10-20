# T088P133 manuscript round 1

This is a complete mathematical **draft implementation**, not an independent manuscript review, acceptance-ready package, portable release, or publication. Formal integration is pending. Campaign count remains 18/20; this implementation assigns no gate or count change.

The theorem is unchanged: every convex four-polytope with nonempty interior and at most six actual irredundant facets satisfies V4(Pi K) <= (160/3)V4(K)^3, with h(Pi K)(u)=V3(K|u-perp), equality exactly for simplices. Every six-facet case is strict, without simplicity, distinct Gale knots, positive interior gaps, or genericity assumptions.

- `main.tex`, `references.tex`, `witness-tables.tex`: full manuscript source, bibliography, all 248 nonzero coefficient terms across ten patterns.
- `output/pdf/main.pdf`: final draft PDF.
- `renders/page-*.png`: final 120 dpi page renders, each visually inspected; see `qa/visual-inspection.json`.
- `support/`: unchanged original author certificate and floating geometry code; unchanged later independent recurrence and exact witness; new reproduction and layout-check scripts.
- `COVERAGE.md`, `PROVENANCE.md`, `RIGHTS.md`: mathematical scope, source/reading limits, formal status, rights and operational boundaries.
- `source-reading-records.json`: source hashes and actual read extents; body files remain private.
- `HANDOFF.md`: parent requirements for a later immutable draft; no active formal files are read here.
- `verify.py`: read-only artifact verifier requiring detached FINAL/MANIFEST/outsideREPORT SHA-256 anchors supplied by the caller.

Author: Myeongjin Kang; no affiliation or contact details. Original prose CC BY 4.0, original code MIT. Retained code notices remain intact. Third-party source/primary/history bodies and derivatives are outside this public draft payload under `../../private/`; they are not licensed by this README and must not be inserted into a portable release.

## Build and reproduce

Run from the draft root (the directory containing `packet/`):

```sh
python3 -B packet/public/bootstrap.py
bash packet/public/build.sh
python3 -B packet/public/support/independent_certificate.py build/checks/rebuilt-witness.json
cmp packet/public/support/certificate-witness.json build/checks/rebuilt-witness.json
python3 -B packet/public/support/author-certificate.py > build/author-certificate.log
python3 -B packet/public/support/geometry_control.py > build/geometry-control.log
```

The bootstrap fetches the pinned Tectonic 0.17.0 Linux x86_64 musl binary, authenticates its archive and binary hashes, and installs only under this draft root. System Python 3, `pdftoppm`, `pdftotext` and `pdfinfo` are required. Tectonic downloads its TeX support on the first build into this root's `build/cache/`; subsequent builds can use the same cache. The exact actual cache inventory is kept privately for this draft. No TeX shell escape is allowed. An existing compatible binary can be selected with `TECTONIC_BIN`, but byte-reproducibility then is not promised. All build outputs, temporary files, caches and renders stay within the assigned root. A sealed copy should be verified before any rebuild; build into a new copy if preserving its exact artifact set. The sealed payload files are read-only; make only that disposable copy writable before rebuilding (for example, `chmod -R u+w COPY/packet/public`).

`build.sh` reproduces all ten exact polynomials, checks the retained witness and table bytes, compiles with two reruns and fixed `SOURCE_DATE_EPOCH`, rejects missing citations/references and overfull boxes, and renders. It does not replace manual visual inspection or independent mathematical review. The author certificate's main function also runs an explicitly labelled Monte Carlo diagnostic. The new reproduction driver checks the exact polynomial content separately. The floating geometry run checks 40 generated examples only and is not part of the proof.

A negative coefficient in the n=5 control rejects that coefficient certificate, not the inequality. The manuscript and reproduction report separately provide exact corner formulas and the rational n=5 auxiliary counterexample. These make no geometric claim in dimensions 5-8.

The original round-3 crosscheck code was fully read and is preserved privately as evidence. Its original relative file layout and round-2 dependency are not transplanted into this support directory. The new reproduction driver compares all five author/round-3 polynomials, authenticates the original full witness bytes, proves the cleared two-bracket identity by exact symbolic operations, and checks the separate rational auxiliary example. It does not claim to rerun round-2 interpolation.

Integrity verification requires externally supplied anchor values; a self-described manifest alone is not a trust anchor. Commands and final detached hashes are in the outside implementation report and handoff response. The verifier checks artifacts, not correctness, novelty, formalization, rights clearance or acceptance.
