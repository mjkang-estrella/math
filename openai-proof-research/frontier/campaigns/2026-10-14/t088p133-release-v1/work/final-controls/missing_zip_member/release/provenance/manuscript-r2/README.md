# T088P133 manuscript round 2

This is the **final-manuscript implementation for independent review**. The completed independently reviewed scoped formal support is integrated. This is not an independent manuscript review, acceptance-ready package, portable release, or publication. Campaign count remains 18/20; this implementation assigns no gate or count change.

The theorem is unchanged: every convex four-polytope with nonempty interior and at most six actual irredundant facets satisfies V4(Pi K) <= (160/3)V4(K)^3, with h(Pi K)(u)=V3(K|u-perp), equality exactly for simplices. Every six-facet case is strict, without simplicity, distinct Gale knots, positive interior gaps, or genericity assumptions.

- `main.tex`, `references.tex`, `witness-tables.tex`, `formal-appendix.tex`: full manuscript source, bibliography, all 248 nonzero coefficient terms across ten patterns.
- `output/pdf/main.pdf`: final implementation PDF.
- `renders/page-*.png`: final 120 dpi page renders, each visually inspected; see `qa/visual-inspection.json`.
- `support/`: unchanged original author certificate and floating geometry code; unchanged later independent recurrence and exact witness; new reproduction and layout-check scripts.
- `COVERAGE.md`, `PROVENANCE.md`, `RIGHTS.md`: mathematical scope, source/reading limits, formal status, rights and operational boundaries.
- `source-reading-records.json`: current source hashes and read/reuse extents; unchanged r1 records are separately labelled historical; body files remain private.
- `HANDOFF.md`: parent requirements for independent final manuscript review and later parent decisions.
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

For this round the authenticated r1 engine and populated cache were copied locally, preserving their metadata/rights; no download was needed. The optional bootstrap fetches the pinned Tectonic 0.17.0 Linux x86_64 musl binary, authenticates its archive and binary hashes, and installs only under this draft root. System Python 3, `pdftoppm`, `pdftotext` and `pdfinfo` are required. Tectonic downloads its TeX support on the first build into this root's `build/cache/`; subsequent builds can use the same cache. The exact actual cache inventory is kept privately for this draft. No TeX shell escape is allowed. An existing compatible binary can be selected with `TECTONIC_BIN`, but byte-reproducibility then is not promised. All build outputs, temporary files, caches and renders stay within the assigned root. A sealed copy should be verified before any rebuild; build into a new copy if preserving its exact artifact set. The sealed payload files are read-only; make only that disposable copy writable before rebuilding (for example, `chmod -R u+w COPY/packet/public`).

`build.sh` reproduces all ten exact polynomials, checks the retained witness and table bytes, compiles with two reruns and fixed `SOURCE_DATE_EPOCH`, rejects missing citations/references and overfull boxes, and renders. It does not replace manual visual inspection or independent mathematical review. The author certificate's main function also runs an explicitly labelled Monte Carlo diagnostic. The new reproduction driver checks the exact polynomial content separately. The floating geometry run checks 40 generated examples only and is not part of the proof.

A negative coefficient in the n=5 control rejects that coefficient certificate, not the inequality. The manuscript and reproduction report separately provide exact corner formulas and the rational n=5 auxiliary counterexample. These make no geometric claim in dimensions 5-8.

The original round-3 crosscheck code was fully read and is preserved privately as evidence. Its original relative file layout and round-2 dependency are not transplanted into this support directory. The new reproduction driver compares all five author/round-3 polynomials, authenticates the original full witness bytes, proves the cleared two-bracket identity by exact symbolic operations, and checks the separate rational auxiliary example. It does not claim to rerun round-2 interpolation.

Integrity verification requires externally supplied anchor values; a self-described manifest alone is not a trust anchor. Commands and final detached hashes are in the outside implementation report and handoff response. The verifier checks artifacts, not correctness, novelty, formalization, rights clearance or acceptance.

## Reviewed formal support and portable reproduction

`formal/implementation/` and `formal/review/` contain UNCHANGED public sources, notices, pins, coverage, historical scripts and receipts. `formal/origin.json` records every origin/hash; `formal/historical/` retains the original FINAL/MANIFEST/outsideREPORT. Pending-at-submission statements inside these unchanged records are historical. Current coverage is Appendix C and COVERAGE.md: 21 support declarations (3 definitions/18 theorems), 20 controls, 15 independent contracts/use-site declarations. Only propext, Classical.choice, Quot.sound occur. The parent adopted PASS_SCOPED_SUPPORT with no repairs; no full theorem is formalized.

From a fresh writable copy of this manuscript root:

```sh
python3 -B packet/public/support/formal_reproduce.py \
  --lean /absolute/path/to/lean-4.34.1/bin/lean \
  --cache /absolute/path/to/trusted/.lake/packages \
  --output "$PWD/build/work/formal-fresh"
```

This NEW relative wrapper copies only supplied source/pins/rebuild.py into its own build/work package, compiles support/controls/audit and prints all actual types/axioms. It also repeats the ten exact rational checks and two added-premise type-contract mutations. It was tested in a separate copied context containing no manuscript/author/private inputs. Historical inventories are metadata only and are not execution dependencies. The unchanged `formal/review/replay.py` hardcodes the original project/implementation path and historical source archive: it is NOT standalone portable reproduction and is not called by the new wrapper. Likewise original verifier/inventory scripts describe their own original seals, not this manuscript's enclosing seal.

Supply trusted Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 plus eight pinned auxiliaries. Only own sources are rebuilt. No clean-source dependency rebuild or complete binary-cache authentication is claimed. No cache binaries or private bodies are bundled in public support. New compilation receipts are under qa/formal/; historical receipts remain attributed under formal/.

The full probability/geometry proof, all 248 coefficients, zero/repeated/nonsimple strata and simplex iff equality are preserved. The scalar-majorization audit assumes its scalar premise; it does not prove expectation-to-mixture comparison. See the complete exclusions in COVERAGE.md. The r1 PDF's all-page QA and same-cache byte identity are historical implementer observations; the parent intake was sampled layout only. New all-page QA and tested-engine/cache reproduction are documented separately for this PDF. No clean offline release is claimed.

Cache observation: all415 copied cache file bytes and the engine binary still match r1. The local build refreshed33 fontconfig-cache mtimes (modes unchanged); these local metadata differences are recorded in the private r2 cache inventory. No original cache was written. Same-cache reproduction claims concern the two actual final r2 runs, not an untouched-cache metadata assertion.
