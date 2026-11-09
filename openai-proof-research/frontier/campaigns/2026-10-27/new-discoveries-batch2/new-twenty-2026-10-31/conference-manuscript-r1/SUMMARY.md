# MathDB 324342 manuscript dossier (conference-manuscript-r1): DRAFT, zero accepted credit

This lane delivers a draft manuscript and a reproducible dossier for MathDB 324342, Conjecture 5 of Etzion, Vardy and Yaakobi (arXiv:1210.5725), which is Conjecture 1 in IEEE Trans. Inform. Theory 59(10), 2013. The work was done by Claude Opus 5.5 with no child agents. No credit has been accepted; root alone accepts. The campaign count (34/40 beyond 39) was not touched.

## The result

The conjecture is false. W is an explicit skew conference matrix of order 20: W = H − I, where H is the Goethals–Seidel array of the sequences
- a = (1,1,1,−1,−1),
- b = c = (1,1,1,1,−1),
- d = (1,1,−1,1,−1).

Let C be the row code of W over 𝔽₁₉.
- **Dimension.** dim C = 10, as the source's Theorem 4 predicts.
- **A weight-9 codeword.** Take x = (5,7,13,9,0,15,14,2,8,18,0,…,0). Then c = xW mod 19 has weight 9, with support {5,8,9,10,12,14,15,16,17}.
- **Conclusion.** d(C) ≤ 9 < 11 = (p+3)/2 = n − k + 1, so C is not MDS.

The credited scope is narrow: the explicit matrix and the word of weight at most 9. The following are background or ordinary computation only and are not credited:
- the exact value d = 9 and the 180 projective weight-9 words;
- the Paley / Reed–Solomon fact;
- the two-class dichotomy at order 20;
- whether p = 19 is minimal.

Lean proves d ≤ 9, not d = 9.

## The paper

The paper is `conference-324342-draft.pdf`: 6 pages, sha256 `6197890a…4228`. Its title is "A skew conference matrix of order 20 whose row code over 𝔽₁₉ is not MDS: a counterexample to a conjecture of Etzion, Vardy and Yaakobi". The source is `dossier/paper/manuscript.md`, built by `dossier/paper/build_paper.py`.

**How it presents itself.**
- It is labelled a DRAFT and AI-assisted.
- It names no human author or affiliation.
- It states modest significance (a qualified pass at the minimum threshold) and makes no priority claim.

**Contents.**
- **Source definitions and text, from the arXiv v2 text and the rendered journal pages.**
  - The weighing and conference matrix definitions, the lattice Λ(W) and the source's rank definition.
  - The row-code ↔ Λ(W) mod p equivalence, which Lean proves for every p, n and W.
  - The Singleton bound and MDS.
  - Theorem 4, Conjecture 1 and the Paley remark, quoted verbatim from journal p. 6715, plus open problem 2 from p. 6722.
  - A four-version comparison table and the MathDB literal.
- **The counterexample.**
  - The full 20 × 20 matrix.
  - A proof that it is a skew conference matrix, via autocorrelations and Goethals–Seidel block identities.
  - The rank-10 argument: self-orthogonality gives ≤ 10, and an explicit 10 × 10 inverse B₀ gives ≥ 10.
  - The coefficient vector, the integer vector xW and the codeword c, so the reader can check every coordinate by hand.
  - A normal-form remark.
- **Supporting computation and background**, marked "not claimed": exact d = 9, the Paley/Reed–Solomon fact, Ball's Corollary 9.2, and what is not established.
- **The formal correspondence.**
  - A definitions table and the verbatim `Conjecture5` statement.
  - The endpoint and its companion theorems; the Paley p = 3 non-vacuity control.
  - The audits (90 declarations by axiom audit, 116 by metadata audit).
  - The import-only replay-fit change, the root's capped replay and the trust limits.
- **Related work and the prior-art limits, stated plainly.**
  - The Arasu–Gulliver body (§2 and its tables) was not read. Its constructions, as described by Armario–Frau, are impossible at p = k = 19 and give length 40; a possible length-n row-code remark in that body is not excluded.
  - The Grassl–Gulliver body was not read (low risk).
  - The search was bounded.
- **Bibliography: 12 entries.** DOIs are given only for TIT 2013, Arasu–Gulliver and Grassl–Gulliver, which are verified by the Crossref receipts in `dossier/sources/receipts/`. Unread bodies are marked as such.

**PDF checks.**
- All 6 pages were rendered at 110 dpi (`qa/page-1..6.png`) and every page was inspected visually. The receipt is `receipts/pdf-qa.json`.
- The text is in `qa/paper-text.txt`. Digits are separated from words everywhere except identifiers such as sha256 and Lean names.
- All fonts are embedded.
- Six issues found during inspection were fixed:
  - an orphan page 7;
  - an unembedded Helvetica font coming from a table default;
  - QED marks placed before the displays;
  - sub- and superscripts colliding with adjacent lines;
  - a wrong cross-reference;
  - a code box overhanging the margin.
- The builder asserts that the printed W, B₀, x, xW, c and its support equal the data in the Lean packet.

## The Lean packet (reused byte-identically; Lean was not run here)

- **Packet.** `dossier/lean/324342-replay-fit-source.zip`, sha256 `c6977a39…a00f`, identical to both the replay-fit-r1 copy and the conference-parent-final-r1 copy. `dossier/lean/packet/` holds its four members, byte-identical; see `receipts/lean-identity.json`.
- **Extraction test.** A safe-extraction test (no Lean) passed: 4 regular members, no absolute paths or `..` components, CRCs verified (`receipts/lean-safe-extraction.json`).
- **Changes from the frozen r4 packet.**
  - The main module's body after the import lines is identical to the frozen r4 module.
  - The only change is the import lines: `import Mathlib` was replaced by six specific modules (`dossier/lean/324342-imports.diff`).
  - Audit and Controls are identical to r4.
- **Root's replay.** The root replayed the packet and it passed. Copies of the logs are in `dossier/receipts/root-replay/`.

## The dossier

- **Core documents:** `dossier/PROOF.md`, `dossier/REPRODUCE.md` and `dossier/MANIFEST.json`.
- **The MathDB raw line:** `dossier/mathdb/324342.raw.jsonl`, line 3870 of chunk 0002 (chunk sha256 `d944c503…ea0a`). The line sha256 is `73a0bb42…1342` without the newline and `12a701a2…c55f` with it. These are the hashes previously recorded by the fidelity review and held-reopen-r1 respectively; the two recordings reconcile.
- **Sources:**
  - arXiv v1 and v2 (PDF and text);
  - the ISIT 2013 author copy;
  - the author-posted IEEE TIT copy (sha256 `a7b49ca6…c9f9`), with r3's rebuild scripts and the rendered journal pp. 6712, 6715 and 6722;
  - the secondary texts: Armario–Frau, the Ball preprint, Araya et al. and Harada–Munemasa;
  - the fetch and Crossref receipts.

  All are copied byte-identically (`receipts/copy-receipt.json`, 114 files).
- **Reviews and rulings:** the reviews and rulings for this candidate, and its history (r4 and the parent revision).
- **Independent stdlib check.** `dossier/tools/check_witness.py` reads the matrix straight from the Lean source inside the ZIP and confirms the following:
  - the conference and skew properties;
  - the Goethals–Seidel reconstruction;
  - rank 10 by fresh elimination;
  - the B₀ and D certificates;
  - the weight-9 word;
  - the Arasu–Gulliver congruences, which have no solutions.

  ALL_CHECKS_PASS; the output is `dossier/data/witness-check.json`.

## Archives

- **Source ZIP.** `conference-324342-source.zip`, sha256 `bf8c9fa2…6193`, 21 members, with manifest `source-manifest.json`.
  - It was safely extracted (`receipts/source-zip-extraction.json`).
  - `check_witness.py` re-ran on the extracted copy and produced byte-identical JSON.
  - The PDF rebuilt from the extracted copy is byte-identical to the lane PDF (`receipts/source-zip-verification.json`).
- **Full dossier ZIP.** `conference-324342-full-dossier.zip`, sha256 `c9122873…ba80`, 249 members. It contains the dossier, the PDF, the source ZIP, `qa/`, `receipts/`, `scripts/`, TASK.txt and launch.json. It was verified by a fresh safe extraction against `full-dossier-manifest.json` and the current lane files: PASS (`full-dossier-verification.json`).
- **What sits outside the ZIPs.** SUMMARY.md, results.json, ARCHIVES-SHA256.json, the two full-dossier JSONs and `frozen-final-check.json` describe the ZIPs, so they are kept outside them. The receipts of the call that built the full ZIP and of the verification calls are outside it for the same reason.

## Integrity and conduct

- **Frozen inputs.** 1,126 frozen input files were hash-bound before any copying (`receipts/frozen-before.json`). They covered:
  - all listed input lanes;
  - the corpus chunk;
  - the three AGENTS files;
  - the reportlab source tree;
  - TASK.txt and launch.json.

  The files were identical after the work (`receipts/frozen-after.json`) and again at the very end (`frozen-final-check.json`).
- **Capped computation.** Every computation ran through `scripts/capped.sh`, one call at a time. That script pins 2 CPUs and sets RLIMIT_CPU 120 s, a 140 s wall timeout, a 2 GiB address-space limit and MALLOC_ARENA_MAX=2, with a lane-local TMPDIR. Receipts are in `receipts/calls/`.
  - Calls: 27 receipts in all.
  - Peak RSS: 56.7 MB.
  - Maximum CPU time: 0.9 s.
- **Small uncapped commands.** Some small inline commands were run directly in the shell without the wrapper, each in well under a second: file listings, `sha256sum`/`cmp`/`diff`, `cp -a` of the reportlab subtree, and short `python3 -I` text edits and one-liners. All Python ran with `-I`.
- **Failed attempts, disclosed:**
  - The first `check-witness` run failed on a parser assertion in my own script. The script was fixed and rerun; that receipt was overwritten.
  - The first `pdf-build-1` failed because the copied Pillow is built for CPython 3.14 and the system interpreter is now 3.15. The diagnosis is kept in `receipts/calls/pil-probe.*`. The fix was to use a hash-identical pure-Python reportlab subset (`receipts/rldeps.sha256`) together with the system Pillow 12.3.0. No network install was made.
- **What was not done:** no Lean, lake, leanchecker, SAT or ILP; no network access; no git; no publication or upload; no external messages; no browser; no shared-ledger edits; no writes outside this lane. `tmp/` is lane-local scratch.
- **Running jobs.** None of this lane's jobs were running at handback (`receipts/no-running-jobs.json`).

## Limits

- The prior-art search was bounded:
  - the Arasu–Gulliver §2 and tables were not read;
  - the Grassl–Gulliver body was not read;
  - 7 citing bodies were read and the rest screened by title only;
  - the registries were checked by path screens.

  There is no worldwide clearance and no priority claim.
- The journal text was read from an author-posted copy, not from a publisher retrieval.
- Statement fidelity is a judgment made by human reviewers. Theorem 4 is not formalized in general.
- Prebuilt Mathlib objects are trusted.
- The two-class dichotomy and minimality are not established.
