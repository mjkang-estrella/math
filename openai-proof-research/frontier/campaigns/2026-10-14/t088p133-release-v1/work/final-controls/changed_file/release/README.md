# T088P133 portable local release v1

Author: **Myeongjin Kang**. This local archive preserves the reviewed 20-page paper, all four TeX files, exact witnesses and reviewed Lean source unchanged. It is prepared for the parent's independent extraction/replay/adoption. **No acceptance, count, release gate, publication, upload, submission or human peer review is assigned here.** Campaign context remains 18/20, two remaining. Publication/uploads/submissions/contacts/browser UI are stopped.

For **every convex four-polytope K with nonempty interior and at most six actual irredundant facets**, with h(Pi K)(u)=V3(K projected to u-perp), the theorem is

    V4(Pi K) <= (160/3) V4(K)^3,
    with equality if and only if K is a simplex.

Every six-facet case is strict, including nonsimple, repeated-Gale, zero and boundary strata. No genericity assumption, >=7-facet/general-body result, dimension5-8 result, optimal auxiliary constant, positive all-n threshold, worldwide priority or current-open-status claim is added. Revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated true; this release performs no upstream truth audit.

The parent separately adopted contribution **SUBSTANTIAL** (its correctness condition discharged), correctness **PASS_FULL_T088P133**, scoped formal **PASS_SCOPED_SUPPORT**, and final manuscript **PASS_FULL_MANUSCRIPT_T088P133**, with no required revisions. Original dispositions are under `provenance/parent/`. Optional reference13 bibliography compaction is not required and is not applied. The PDF's truthful implementation-at-time-written status is unchanged; this enclosing later record reports the subsequently adopted manuscript review. Historical README/HANDOFF/FINAL text is attributed history, not the current release instructions or a new review request.

## Contents and exact coverage

`packet/public/output/pdf/main.pdf` is the unchanged final paper (SHA256 c4e15a10f86623abe2919c36f4863971cea611d705dd3bcbc9684cff260a8647). The full source is `packet/public/{main.tex,references.tex,witness-tables.tex,formal-appendix.tex}`. Main TeX SHA256 is b5000cb9a3df1684fa94915ac11bd11d91254455f13be43c8a396c51051fe5b6. All 248 witness/table terms, ten patterns and five polynomials are supplied, with original author certificate, later independent recurrence and independent direct-residue checker. The geometry code is retained as a floating diagnostic, not a proof and not required by release reproduction.

`assembly-map.json` explicitly identifies every copied file, origin hash, role and omitted category. Copied bytes, mathematical source, reviewed code and notices are unchanged. New root scripts adapt routing only. `formal/origin.json` is the unchanged original 53-file ledger; this selected release includes only its execution/coverage/rights subset. Omitted historical inventories, sealers and `formal/review/replay.py` are not dependencies. That old replay hardcodes its original companion/project and is nonstandalone. Its bytes were not edited or described as portable. The retained reviewed rebuild script has historical tool defaults; our runner always supplies explicit --lean/--cache.

Scoped Lean support is exactly **21 support declarations (3 definitions, 18 theorems), 20 controls, 15 independent semantic/type/use-site audit declarations**. Only propext, Classical.choice and Quot.sound occur. For real alpha,beta,p,q,d,P,N, the strict interface requires alpha,beta>0, alpha+beta=2, 0<p<1, q=1-p, d>=0, P,N>0, 2dp²<P, 2dq²<=N and proves

    (1+d)[p alpha/(alpha+P/p) + q beta/(beta+N/q)] < 1.

The non-strict interface, derived denominator/bracket signs, moment conversions, d=0 and reduced endpoints are covered. `one_sided_lt_one` correctly requires no d>=0. The independent normalized bracket/type mapping and `scalar_majorization_use` are covered, but the latter has an **explicit assumed scalar premise**: expectation comparison is not formalized. The runner reproduces all56 actual types/axioms, ten rational configurations and two added-premise semantic mutation rejections.

**Entirely unformalized:** actual-facet geometry/nonzero-middle exclusion; mixed volumes, maximum/attainment, coarea and Gamma/Dirichlet; distributions, log-concavity, HNBUE and expectation-to-mixture majorization; ten-pattern certificate and its probabilistic interpretation; continuity, zero/repeated-knot/strata assembly and strict-moment derivation; simplex equality, every-six-facet strictness, and the full geometric theorem. The paper supplies these mathematical arguments; finite exact checks and Lean algebra do not replace them. See original COVERAGE and formal notices/review for complete mappings.

## Authenticate before executing

The handoff supplies independent full SHA256 values for **FINAL.json, MANIFEST.json, outside REPORT.md and release.zip**. Obtain those four values from the parent/handoff, never trust a candidate-local sidecar as its own authority. FINAL binds the other three and the verifier SHA. MANIFEST is included in the ZIP and separately supplied. It covers all other files and exact directories; ZIP includes explicit directory entries, fixed timestamps, stored compression and Unix modes (files0444, directories0755). No absolute paths, `..`, duplicate names, symlinks, hardlinks, special files or extra entries are accepted.

Bootstrap with trusted Python standard-library hashing: check the outside FINAL bytes against its independently supplied SHA before parsing it, then check the distributed `verify.py` bytes against `verifier_sha256` in that authenticated FINAL. Inspect the short verifier if needed. The verifier only reads/prints: no payload execution, compilation, extraction, downloads or cache/report writes. The four external anchors and supplied verifier authenticate executable bytes before they run.

```sh
# F, M, R, Z are independently supplied full hexadecimal handoff values.
# Run from a working directory outside the immutable extracted release.
python3 -B /path/to/trusted-verified/verify.py \
  --final /path/to/FINAL.json --final-sha256 "$F" \
  --manifest /path/to/MANIFEST.json --manifest-sha256 "$M" \
  --report /path/to/REPORT.md --report-sha256 "$R" \
  --archive /path/to/release.zip --archive-sha256 "$Z"

# This writer refuses existing output. It performs exact path/member checks.
python3 -B /path/to/trusted-verified/archive.py extract \
  --archive /path/to/release.zip --manifest /path/to/MANIFEST.json \
  --output /absolute/fresh/extracted

# Repeat the first verification command with --root /absolute/fresh/extracted.
```

`archive.py`, `reproduce.py` and `integrity_controls.py` must first match the manifest in the authenticated ZIP. To bootstrap extraction without executing an unverified bundled writer, use a trusted ZIP inspection/extraction tool with the exact checks stated above, or independently compare the writer's bytes to its authenticated manifest entry. A seal authenticates artifacts; it awards no mathematical, novelty, rights or acceptance verdict.

## Reproduce from the fresh extraction

All writing commands require a **fresh specified output directory outside the immutable extracted root**. They copy supplied sources into disposable compatible layouts; every run compares the extraction's full inventory before/after. All TMP/XDG/build/cache outputs are routed beneath that new output. No original author, proof, manuscript, formal-source, project tree or private inventory is an execution dependency. Do not execute historical commands in attributed prose.

Explicit trusted inputs are system Python3.10+; SymPy1.14.0 with mpmath1.3.0 for the independent residue check; Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and precompiled mathlibd13f23b723b8a846827a245b89c10fc7d3f11612 plus eight auxiliary pins in the supplied lake-manifest; Tectonic0.17.0 binary SHA256 a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da and the declared populated TeX cache; Poppler `pdftoppm`, `pdftotext`, `pdfinfo`; and their Linux runtime/system font environment. `tool-inputs.json` gives the exact415 TeX-cache file hashes/sizes, derived from the separately authenticated original inventory. No binaries/caches/dependency bodies are bundled. TeX cache is copied before use, never written in place. Tectonic runs `--only-cached --untrusted` with SOURCE_DATE_EPOCH1792454400.

```sh
python3 -B /absolute/fresh/extracted/reproduce.py all \
  --output /absolute/fresh/reproduction \
  --python-path /absolute/installed/sympy-and-mpmath \
  --lean /absolute/lean-4.34.1/bin/lean \
  --cache /absolute/trusted/.lake/packages \
  --tectonic /absolute/tectonic-0.17.0 \
  --tex-cache /absolute/declared/populated-xdg-cache
```

Omit --python-path only when those exact Python packages are already installed in the selected interpreter. Modes `exact`, `formal`, `pdf` run individual components with relevant arguments. `pdf` also reruns the unchanged exact certificate/table driver, checks TeX references/logs, renders20 pages and compares the PDF SHA to the reviewed PDF. Every receipt states actual outcomes and preservation; no new paper replaces the supplied one. Byte identity is promised only as a tested outcome under the declared engine/cache/runtime conditions, not across arbitrary environments. The independent review already inspected every actual PDF page1–20; its attributed receipts are included. This release does not award a new manuscript gate.

This is **clean archive extraction with explicit trusted dependencies**, not OS sandboxing, a network-free from-source toolchain build, clean dependency-source Lean rebuild, or full Lean binary-cache/supply-chain authentication. Lean dependency pins are checked; only own sources compile. There is no installer, global installation or network bootstrap. If a declared dependency is unavailable, supply it explicitly; do not use hidden historical roots.

```sh
# Deterministic reassembly, including exact member bytes/modes/order/timestamps:
python3 -B /absolute/fresh/extracted/archive.py assemble \
  --source /absolute/fresh/extracted --output /absolute/fresh/reassembly
# Compare reassembly/release.zip with the independently anchored original ZIP.

# Copy-only integrity controls, with the same four external values:
python3 -B /absolute/fresh/extracted/integrity_controls.py \
  --root /absolute/fresh/extracted --output /absolute/fresh/controls \
  --final /path/to/FINAL.json --final-sha256 "$F" \
  --manifest /path/to/MANIFEST.json --manifest-sha256 "$M" \
  --report /path/to/REPORT.md --report-sha256 "$R" \
  --archive /path/to/release.zip --archive-sha256 "$Z"
```

## Provenance, positioning and rights

Frozen statement SHA25686e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354 and proof SHA256971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84 remain unchanged. The complete13223-entry upstream path tree has SHA256eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b; truncated tree.json is not used. Manuscript/review envelopes and source hashes are retained as provenance, not claims to bundle their entire historical roots.

PQ1–PQ5 remain: precise bounded class; only project novelty/no antecedent in recorded bounded searches; credit SourceP, FHLX Section4, r132R1–R4/star and classical HNBUE/Klefsjö; transparent exact ten-pattern certificate distinct from floating diagnostics; explicit method limits beyond n=4. Negative coefficients reject a certificate, not an inequality. The separate exact auxiliary corner example is retained without a geometric dimension5–8 claim.

Primary reading debt is unchanged: original reviews read full SourceP and operative FHLX TeX introduction/preliminaries/Section4; FHLX PDF was byte-only; Prékopa Theorem3 and6–8 proofs were read; Saroglou/Petty extents were partial; Klefsjö bodies remain unread; Brannen/CFLXX bodies unavailable. This release hashes/reuses evidence and reads reports/interfaces, without claiming a new primary-body or literature review. The paper's full provenance appendix and retained r1/r2 records preserve exact extents.

The sketch and certificate predate the recorded freeze2026-10-20T17:21:32Z. Original FINAL seal17:31:58.711847Z conflicts with later notes drafting/packaging17:36–17:45Z. Both remain; no preferred clean chronology is invented. Prefreeze work, late reads, temporary-path disclosure, earlier provider network/usage failures, corrected missing-V checker and distinct-only spot-sample limits remain explicit. Old failures were not mathematical verdicts. The review's disclosed traversal/authentication-order/development limitations remain in its original limits.md.

Original paper/prose: **CC BY4.0**, https://creativecommons.org/licenses/by/4.0/ . Original code, including new release routing: **MIT**, full notice at `packet/public/LICENSE-CODE.txt`; all copied formal/review/code notices are retained. Attribution: Myeongjin Kang; no affiliation/contact invented. Release wrappers/documentation/selection are the only new work. Third-party rights are unchanged. Protected primary/upstream/history/search bodies and their derivatives/renders, dependency/cache binaries and engine bytes stay local and excluded. Hash inventories do not confer redistribution rights or establish semantic reading. No public upload of any kind occurs.
changed
