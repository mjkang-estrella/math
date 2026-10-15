# Functional hard-sphere fluctuations on a regular Boltzmann lifespan

Standalone manuscript prepared for an independent manuscript gate. The frozen repaired proof received a full-scope written proof review; this newly typeset presentation has not yet received that gate. No acceptance, campaign count, worldwide priority, submission, or public upload is asserted.

The paper treats the actual unsmoothed deterministic grand-canonical hard-sphere gas in whole space, including the empty configuration, with exact microscopic centering, under precisely H's kinetic hypotheses on the entire supplied regular interval. Its conclusion is finite-test-vector Skorokhod J1 convergence and C-tightness. It makes no weak-convergence assertion for the uniform-topology Borel space on all cadlag paths.

## Files and reproduction

- `main.tex` and `references.tex`: complete paper and inlined bibliography.
- `output/pdf/main.pdf`: compiled 19-page paper.
- `qa/page-01.png` through `qa/page-19.png`: all-page Poppler renders; `qa/visual-qa.json` records visual inspection.
- `source-map.md` / `.json`: 25 claim groups, credited interfaces, new deductions, and exact TeX labels/lines.
- `inputs.json`: immutable input paths, SHA256 values, and byte lengths. These are project-root-relative.
- `source-H.json`: ten pinned upstream paths, raw URLs, SHA256, Git blob SHA1, lengths, and read extents.
- `editorial-response.md`: E1-E7 and proof-interface response map.
- `provenance.md`: reading, attribution, historical errata, and verification limits.
- `validation.json`: automated structural checks only; `outputs.json` authenticates deliverables other than itself.

From this directory, with Python 3, Tectonic, and Poppler installed:

```sh
python3 build.py --tectonic /path/to/tectonic
python3 checks/repair_checks.py
python3 checks/adversarial_checks.py
python3 checks/editorial_checks.py
python3 verify_sources.py --project-root /path/to/openai-proof-research
python3 verify.py --project-root /path/to/openai-proof-research
```

The supporting scripts write their receipts only inside this directory. `build.py` generates PDF, log, text extraction, and every-page renders. TeX needs no external bibliography run. A fresh build is expected to reproduce content and layout; PDF metadata or engine versions can change byte hashes. Re-inspect the new renders if rebuilding. The original rendering used Tectonic at `/tmp/frontier-typeset/tectonic` and Poppler at 105 dpi.

Both verifiers parse an explicit `--project-root` before attempting automatic root discovery. Without that option they search ancestors for `AGENTS.md` and `sources/upstream.json`; an external copy lacking those markers requests the option with a clear argument diagnostic. A post-freeze portability repair removed an eager fixed-depth parent lookup. `qa/portability-check.json` records successful verification of a disposable shallow copy and preservation of the paper/PDF hashes.

For a portable source check without the local cache, `verify_sources.py --fetch --project-root /nonexistent` downloads the exact pinned raw bytes into a disposable directory under `tmp/` and removes them afterward. It never restores or edits shared sources. The paper itself builds without H's source cache. Full input verification requires the surrounding frozen research records, whose paths and hashes are supplied in `inputs.json`.

## Verification scope

The fourteen named repair controls, eight named editorial controls, and copied exact counterchart calculations use rational arithmetic or finite polynomial identities. They check a finite chronology obstruction and repair samples, structural O-tie rejection, initial-link shears, energy/scaling identities, factorial diagonals, and exponent arithmetic. They do not prove history existence, a Jacobian or measure identity, the window estimate, uniform remainder estimates, tightness, or a stochastic limit. The copied repair/adversarial program bytes and result bytes agree with the frozen repaired candidate's companions.

No full Lean certificate exists for the theorem. The separately compiled `kinetic-formal-v1` has nine supporting declarations: elastic-pair momentum and squared-norm energy; four affine time-shift identities; finite all-line energy under a pair replacement and its concrete elastic specialization; rational exponent arithmetic. Its compiler/axiom receipts are inputs, not mathematical premises of the paper. It does not formalize the entering-root construction, strict-prefix chronology covariance, determinants, Jacobians, history existence, any analytic estimate, or path convergence. A completed independent semantic/fresh-compilation audit subsequently returned PASS for exactly those nine algebra statements, with fourteen audit declarations and four rejected mutations; its review and parent disposition are authenticated inputs. This is not a formal PASS for the analytic theorem. Potential later support targets include the falling-factorial cubic identity, the simultaneous simplex volume, and a fully specified prefix-history recursion. They are not claimed completed.

Author: Myeongjin Kang. No affiliation. Original paper and prose: CC BY 4.0; original code: MIT. Copied programs retain their notices; third-party sources retain their own rights and terms. No external source file is relicensed by this package.
