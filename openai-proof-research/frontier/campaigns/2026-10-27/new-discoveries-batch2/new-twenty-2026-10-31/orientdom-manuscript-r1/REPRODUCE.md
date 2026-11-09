# Reproduce the draft dossier

Run from this dossier's root. All output and temporary paths must stay here. Python scripts use real script paths with `python3 -I`; none depends on `__file__` under stdin. `scripts/cap.py` resolves its root from its real script file and sets local TMPDIR/cache, MALLOC_ARENA_MAX=2, two-CPU affinity, CPU 120 seconds, wall 140 seconds, per-process address-space ceiling 6 GiB and a sampled process-group RSS watchdog at 6 GiB. No network or solver is needed. Run one heavy process at a time, in the foreground. The sampled watchdog is not an instantaneous cgroup guarantee.

## Integrity and extraction

`python3 -I scripts/cap.py verify-manifest python3 -I scripts/verify_manifest.py`

The verification reads `PAYLOAD-MANIFEST.json`, then tests ZIP CRCs and internal archive SHA-256 manifests. The manifest excludes itself and subsequent packaging/verification receipts to avoid circular hashes; `ARTIFACTS.sha256` covers these outer artifacts. Full dossier snapshots include all 646 frozen input files, including original acquisition failures, reports and historical logs. Their inclusion does not imply every unrelated candidate in the discovery lane was rereviewed here.

If the original sibling lanes are present, run `python3 -I scripts/cap.py verify-inputs python3 -I scripts/verify_inputs.py` to compare them with both before/after inventories and copied bytes. Without the sibling lanes, the recorded before/after manifests and snapshot hashes remain independently inspectable; do not invent an original-source comparison.

Run `python3 -I scripts/cap.py packet-retest python3 -I scripts/safe_extract.py tmp/packet-retest-new` with a fresh lane-local destination. The packet remains byte-identical to the supplied `Lean-packet.zip`, SHA-256 `3d9361bef2cc188b191519cd9718e4d983ccbe6b17df8dec6448dcf5228ab1d6`. Extraction checks names, types, duplicate names, total expanded size and extracted member bytes. It does not execute Lean or establish proof validity.

## Recompute the mathematical values

For each n in 3, 4, 5, 6 and each b in 0, 1, 2, sequentially run:

```
python3 -I scripts/cap.py enum-nN-bB python3 -I scripts/recompute.py N B
```

Replace N and B with the indicated integers and use matching receipt names. Each branch fixes the absent/forward/backward state of the first unordered vertex pair. Each run is independently capped. It visits all assignments to the remaining pairs, filters positive indegree, and computes the minimum dominating-set cardinality by exact subset testing. Do not run the three branches concurrently.

Then run:

```
python3 -I scripts/cap.py aggregate python3 -I scripts/aggregate.py
```

This recomputes all per-graph spectra and connected/all-graph totals, checks absence of gaps, compares the supplied discovery/review counts and tests the printed directed-cycle examples using a separate all-subset routine. The historical counts are comparison targets, not enumeration inputs. The order-6 branches completed well inside the caps; receipts preserve elapsed time, sampled RSS and exits. The theorem is proved in `PROOF.md`; enumeration is supporting evidence only.

## Rebuild and render the paper

The source template is `paper.md`; `scripts/build_paper.py` resolves its two tables and exact root-ruling quotations into the complete editable `paper.fodt`. `paper-expanded.md` is a fully resolved reading copy. Source requirements: Python standard library, local Liberation Serif font, LibreOffice Writer and Poppler. No package installation is required. The initial ReportLab attempt failed due to a missing local module; its unused script and failure receipts remain as provenance, and it is not the final build route.

```
python3 -I scripts/cap.py build-source python3 -I scripts/build_paper.py
```

For PDF export, use `libreoffice -env:UserInstallation=file:///ABSOLUTE/DOSSIER/tmp/lo --headless --convert-to pdf --outdir . paper.fodt` through the cap wrapper, replacing ABSOLUTE/DOSSIER with this dossier's actual absolute root. The local profile option is mandatory to keep writes here. The delivered PDF used LibreOffice 26.8.2.2; PDF metadata need not reproduce byte-for-byte on later exports.

```
python3 -I scripts/cap.py render-paper pdftoppm -scale-to 1600 -png paper.pdf qa/page
python3 -I scripts/cap.py extract-paper pdftotext -layout paper.pdf qa/paper.txt
```

Inspect every page visually after any rebuild. The delivered five-page version has a hash-bound receipt in `receipts/page-qa.json`. Rebuilding changes receipts and invalidates the original manifest until regenerated. `scripts/finalize_content.py` is the original post-inspection content assembler; its QA statements are observations from this authoring session, not an automated visual checker. Do not use it to attest an uninspected later PDF.

## Formal evidence and trust limits

Do not run Lean, lake, leanchecker or SAT/ILP solvers for this task. The historical Lean instructions inside the byte-identical packet are archival, not an instruction to execute them now. Read `inputs/orientdom-review-r1/REVIEW.md`, its logs, `inputs/orientdom-parent-final-r1/replay-result.json` and the packet source instead. The endpoint is `OrientableTotalDomination.conjecture_true : OrientableTotalDomination.Conjecture`. Historical strict compile, explicit-module kernel checks and all-local-declaration audits report PASS with only propext, Classical.choice and Quot.sound, using pinned dependency oleans. No full upstream rebuild is asserted.

The prior-art qualifications are exact in `PRIOR-ART-LIMITATIONS.txt`, the expanded source and the root-ruling JSON. The 1996 ordinary-domination proof and DAM 2026 version of record remain unread; citing-work coverage is bounded. Earlier HOLD reports and the subsequent qualified proceed ruling are both retained. Registry CLEAN means only the scope described in the parent's refresh receipt. No new access, publication, priority or acceptance claim is made.
