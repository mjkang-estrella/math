# RCS128 manuscript review r1: reading record and limits

Reviewer: independent manuscript review sub-agent (Factory Droid, Claude Opus 5.5). Original prose CC BY 4.0; original reviewer code MIT. Third-party bodies were read in place, are referenced only by path and hash, and are not copied here.

## 1. Read in full

| object | identity | notes |
|---|---|---|
| Manuscript LaTeX: `article.tex`, `sections/01`–`09`, `references.tex` | packet manifest `00b40211…aee05` | every line; compared with candidate and proof review |
| Rendered PDF, all 17 pages | `441f3fac…0a11` | each page image viewed at 130 dpi (see `pages/page-inspection.json`) |
| `verify.py`, `public/build.py` | `5b51763e…94f68` (verify.py) | read before running |
| Author records: `README.md`, `checkpoint.json`, `input-identity.json`, `response-to-findings.json`, `proof-scope-crosswalk.json`, `reading-provenance.json`, `bibliography-audit.json`, `validation/*.json` | in packet manifest | all 83 label/page locations re-resolved against a fresh `.aux` |
| `candidate.md`, `original-scope.txt` | `ebfed67a…`, `7dfa38db…` | full |
| `rcs128-proof-r1/review.md` | manifest `50bf7355…` | full (O1–O11) |
| `rcs128-contribution-r3/review.md`, `findings.json`, `reading-limits.md` | manifest `1d9aba05…` | full (RQ1–RQ5, O1–O6) |
| Author `contribution-and-limits.md` and candidate's "The new work is …" sentence (candidate line 18) | in author manifest `a81ea233…` | full; checked that neither the sentence nor the host/cycle/output rows are carried into the manuscript as novelty (RQ2) |
| `rcs128-formal-review-r2/review.md` | manifest `776eb20b…` | lines 1–11 (verdict) and 120–170 (controls, coverage, findings O1–O7, limits) in full; other sections only through keyword hits (59 declarations, M7 weakened statement, O3–O5 assessments) |
| `rcs128-formal-v1/RCS128.lean`, `Controls.lean` declaration lists | manifest `c3a05186…` | all 16 + 7 theorem names; statements of `final_length_bound`, `odd_core_from_previous_failure`, `first_threshold_core` |
| Parent: `contribution-r3-response.json`, `manuscript-requirements.json`, `comparison-r4/open-findings.json`, `extra-primary/reading-note.json` | sha256 prefixes `54314cad`, `bd7624c1`, `edc8949b`, `e630f14f` | full |
| Parent: `manuscript-r1-brief.txt`, `proof-formal-adoption.json`, `extra-primary/receipt.json` | `proof-formal-adoption` `476a1a5c`, `receipt` `a41ce1f6` | displayed text read; a few long lines were truncated by the display tool, so these are partial readings. `contribution-response-draft.json` and `comparison-r4/reading-checkpoint.json` were hashed but not read; the final `contribution-r3-response.json` supersedes the draft |
| Pinned source sections 02–07 | git-blob SHA1 and sha256 matched `preprints-tree.json` | read in the comparison; all 14 cited labels located in the stated files |
| Fici et al. arXiv 1511.08431v1 extraction | `adaf2cfd…` (PDF `fddcb7e6…`) | lines 1–600, complete |

## 2. Primary sources: exact ranges checked for attribution

| source | file sha256 | lines / pages | what was confirmed |
|---|---|---|---|
| Yamano–Shibuya WABI 2026 | `4defee70…` | 1–40, 70–80, 134–200, 240–248, 260–272, 496–500, 687–705; keyword hits elsewhere (391, 532–535) | Section 2 arbitrary involution formulation; Lemmas 7, 9, 12; Theorems 11, 13; oriented formal copies in Section 4.2 (line 391, MR-O4); JLD summarized as a 3-approximation (lines 75–76); pages 2:1–2:13, DOI |
| Yamano–Shibuya CPM 2026 | `df441f61…` | 1–12, 455–529; keyword hits at 18–36, 55, 70–108, 234–237 | 3.75 and 2.875 theorems; Lemma 18 proof uses the reverse complement of the entire optimal superstring; MGREEDY-RC 4 and suggested TGREEDY-RC 3; pages 15:1–15:11 |
| Fici et al. 2015 | `adaf2cfd…` | 1–600 | Section 2 distinct vertices for word and reversal including palindromes; 3.1 paired arcs/reverse paths; 3.2 palindrome identifiers; Lemma 6 surgery; Theorem 7 compression 1/2; JLD "greedy-like … ratio 4" |
| Goldberg–Karzanov arXiv v2 | `090a64ed…` | 1–20, 176–200, 474–520, 740–756 | fixed-point-free sigma; Theorem 3.1; Corollary 3.2; Section 5 exchange of halves at x and x′ |
| Medvedev et al. 2007 | `ddcbe192…` (text), rendered page 5 image | 268–290, page-5 image | Section 2.2 Lemma 1 (Eulerian iff connected and balanced) |
| Kundeti et al. 2010 | `69b24564…` | 1–12, 350–380 | Section 6, Lemma 1 sufficient Euler condition; author name extraction "Heiu" vs cited "Hieu" (cited form follows parent metadata) |
| BJJ 1996 BRICS RS-96-21 | `3174741d…` | 1–25, 367–374, 575–640 | June 1996; Section 7 "Concluding Remarks" contains the acknowledgement crediting Crochemore's Lyndon min/max-rotation proof |
| Collapsing (arXiv v3) | `c02fd1ed…` | 1–30 and section headings | Sections 2.2 Hierarchical Graph and 7.2 Optimal Cycle Covers exist |
| Mucha 2013 | `7fa4bad7…` | 1–8 and rotation hits | title and rotation material; SODA page range matches Fici reference [14] |

The sha256 values for Medvedev, Kundeti, BJJ, Mucha and Collapsing extractions are those recorded in the author's `reading-provenance.json`; GK, CPM, WABI and Fici were recomputed here.

## 3. Not read, or read only partly

- Jiang–Li–Du 1992 body and Breslauer–Jiang–Jiang 1997 journal body: unread by everyone in this chain. The manuscript uses the parent-selected, reviewer-permitted RQ4 options. No new reading is demanded here.
- WABI Section 5.2, GK Sections 6–10, CPM outside the ranges above, Medvedev and Kundeti beyond the cited lemma sections, Mucha and Collapsing bodies beyond headings and spot reads. These are not needed for any attribution the manuscript makes.
- Fici figure images: not viewed by this reviewer (the parent viewed pages 8–9). The surgery is fully described in the text.
- Bibliographic metadata for Collapsing (LIPIcs 145, article 26) and Mucha's DOI: not checkable against local primary headers; the author's `bibliography-audit.json` discloses the parent-record basis.
- No fresh Lean compilation or kernel replay. Formal statements were read, not rebuilt.
- No re-audit of the full proof. This is a manuscript gate. I checked that the manuscript's mathematics matches the frozen candidate and the proof review's resolutions, and I re-derived spot steps (individual trichotomy forcing q > p; odd-core count 2k+1 > 2k; final chain |T| = U/2 ≤ W ≤ 2 OPT_RC matching `final_length_bound`). I did not recompute W = 6 or W = 12; those come from the author verifier and the proof reviewer's `rc_counts.py`.
- Pinned upstream truths (`fd4aeeb2…`) are stipulated, per AGENTS.md.

## 4. Environment notes

- Rebuild and render ran in `/tmp/rcs128-mr1-work` (copied source, unchanged after builds).
- The `/tmp` tmpfs hit a per-user disk quota during the first control attempt. The partial copy was removed. All negative controls then ran in `/var/tmp/rcs128-mr1-controls`, a real (non-symlinked) directory outside the repository. Both areas are disposable.
- Finite checks in `reproduction/` are diagnostics. None of them proves Theorem 1.1.

## 5. Claims not made

No acceptance, count change, publication, release, worldwide priority, or literature-novelty certificate. The credit boundary is project-relative to the antecedents actually read.
