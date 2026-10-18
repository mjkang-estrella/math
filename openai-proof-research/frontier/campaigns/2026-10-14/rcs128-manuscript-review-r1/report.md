# RCS128 independent manuscript review, round 1

Reviewer: independent manuscript review sub-agent (Factory Droid, Claude Opus 5.5). I am not an author. I wrote only this directory, plus disposable scratch areas in `/tmp/rcs128-mr1-work` and `/var/tmp/rcs128-mr1-controls`. No nested agents, shared edits, staging, commits, uploads or acceptance. Original prose CC BY 4.0; original reviewer code MIT.

## Verdict

**PASS_FULL_MANUSCRIPT_RCS128.** No required finding. Five optional findings (MR-O1 to MR-O5) are cosmetic, editorial or record-keeping.

This is a manuscript gate only. It is not acceptance, a count change (still 12/20), a release, a publication recommendation, or a worldwide-priority certificate. The parent alone accepts. Uploads remain stopped.

## 1. What was reviewed

| object | anchor | result |
|---|---|---|
| manuscript packet `rcs128-manuscript-r1/` | external `00b40211d6c6f7c1361e89953a6e9a0260c230f4e8225b5e81872d52e6aaee05` | `verify.py` read first, then PASS (82 files, 13 dirs) |
| PDF `public/output/pdf/rcs128.pdf` | `441f3fac35dbd6f7623361b7d371ff58fbda3f1aba89a2376810a4f0632a0a11` | rebuilt byte-identically twice |
| candidate, scope | `ebfed67a…`, `7dfa38db…` | rehashed, match |
| author r37, proof r1, formal r2, formal v1, contribution r3 | `a81ea233…`, `50bf7355…`, `776eb20b…`, `c3a05186…`, `1d9aba05…` | rehashed; each packet's verifier run integrity-only: PASS |

The parent resolution files listed in `reading-and-limits.md` were hashed and read to the extent stated there.

## 2. Scope and theorem

Theorem 1.1 and the abstract state the original scope with no narrowing:

- every explicitly encoded finite alphabet and involution;
- every finite family, including empty words, the empty family, duplicates, containment, fixed letters and palindromes;
- a deterministic algorithm, polynomial in encoded bit size;
- output containing s or ρ(s) for each s, with |T| ≤ 2·OPT_RC.

The theorem and abstract say plainly that the result depends on the pinned ordinary source's stronger contracts. The manuscript does not present itself as an independent proof of the ordinary theorem.

The final chain (18), |T| = U/2 ≤ W ≤ 2·OPT_RC, matches the frozen candidate. It also matches the formal `final_length_bound` hypotheses (2·output = upCost, upCost ≤ 2W, W ≤ 2·OPT).

## 3. Mathematics against the frozen candidate and proof review

I read every line of the LaTeX and compared it with `candidate.md` §§1–7 and the proof review. The mathematics is the frozen construction. Changes are presentational or are the proof review's clarifications. The author crosswalk lists 83 label and page locations; I re-resolved all of them against a fresh `.aux` (`reproduction/crosswalk-check.json`): 0 mismatches, 56 labels, no duplicates.

Spot re-derivations:

- **Individual trichotomy (§4.1).** If cases 1 and 2 fail, then b − a > 2p. The agreement bound b − a < p + q then forces q > p, as the text uses.
- **Odd core (Lemma 6.1).** The self-text rule gives at least 2k+1 unblocked occurrences. By the threshold and the exit convention, at most 2k share the identical alignment, so an outside record exists. The previous failed threshold gives 2k−1 core layers. The k = 1 case is handled.
- **Completion (§6.3).** The collective link on 2k−1 layers costs K = kp. The 2k-th layer meets the core through Lemma 3.1. If the test fails, all upper pairs, including the top k, go to the individual procedure.
- **Baseline (§5.2).** Lower pairs share period q in the recipient orbit. Each is rooted with its own budget. The partner-group construction is done first and then reflected.
- **Half-Euler (Lemma 8.1).** The lemma now explicitly requires a fixed root in the used support, and the application at ε satisfies this. Loops are allowed in the general lemma, and the hierarchical graph has none.

Source contracts (§1.1): all 14 cited source labels exist in the stated pinned files. These are `lem:counts` and `lem:base`; `lem:recorded`, `lem:layers`, `lem:matching-window`, `lem:agreement` and `lem:max-rotation`; `lem:ordered-windows`, `lem:band`, `lem:collective` and `lem:host`; and `lem:cycle-contact`, `lem:free-period` and `thm:connection`. The manuscript uses the *proof* of `lem:collective` (2k−1 layers, K = kp) and of `lem:cycle-contact`. It applies `lem:host` only after re-establishing its hypotheses on E. It does not assume `thm:connection` is equivariant.

## 4. Prior findings: every item disposed

Full dispositions with line references are in `findings.json`. Summary:

- **Proof O1–O11:** all implemented. O1 g-cases; O2 labelled-edge splice; O3 vacuous case 1; O4 partner group then reflect; O5 all upper pairs including the top k; O6 p = 1; O7 ≤ q contact and stable IDs; O8 kp+1 interval; O9 minimum-period child among survivors; O10 deterministic equal-period order; O11 loops and fixed root.
- **Formal O1–O7:** all implemented in Appendix A and A.1. The 16 declaration names match `RCS128.lean` exactly, and the 7 controls are in `Controls.lean`. The appendix:
  - attributes the 59 reviewer declarations to the reviewer;
  - discloses that a weakened factor-four statement passes the harness;
  - states module-only replay with trusted `.olean` files;
  - says the main theorem is not formalized.
- **Contribution RQ1–RQ5:**
  - RQ1 is satisfied: the candidate is unchanged and there is no repair.
  - RQ2 is implemented: exactly the three-part package is credited, with an explicit no-credit list. The candidate's "new work" sentence and the author's host, cycle and output novelty rows are not carried over.
  - RQ3 is implemented; each attribution was checked in the primary text (§5).
  - RQ4 is implemented exactly: the parent-selected JLD wording is verbatim, and the BJJ citation is split into a 1997 archival reference and the 1996 operational report.
  - RQ5 is implemented with the stated limits.
- **Contribution optional O1–O6:** implemented. O4 is disclosed as a reviewer diagnostic only.
- **Parent items:**
  - the GK §5 splice antecedent is credited;
  - the Fici predecessor is cited accurately;
  - the author's two editorial clarifications are accepted.

## 5. Attribution checked against primary text

| manuscript claim | primary evidence |
|---|---|
| WABI: arbitrary involution formulation (Section 2), Lemmas 7, 9, 12, Theorems 11–13, 8/3 | extraction lines 134–152, 242, 260, 309, 496, 532 (formal copies are in §4.2, line 391: MR-O4) |
| CPM: 3.75, 2.875; Lemma 18 uses the RC of the entire optimum | lines 104–108, 476–520 ("considering the reverse complement of the entire optimal superstring") |
| Fici: palindrome vertex copies and paired reverse paths (Sections 2–3), Lemma 6 surgery, Theorem 7 is compression 1/2 not length | full extraction; Section 2 V = {v_s} ∪ {v_s^R}; 3.1 paired arcs e, e^R; Lemma 6 Figs. 1–4; Theorem 7 |
| JLD as described later: Fici 4, CPM MGREEDY 4 vs suggested TGREEDY 3, WABI 3 | Fici abstract and line 103; CPM lines 23–25, 78–82; WABI lines 75–76 |
| GK Theorem 3.1, Corollary 3.2, §5 exchange of halves; no fixed vertices in GK | lines 476, 513, 746–749; §2 σ(x) ≠ x |
| Medvedev §2.2 Lemma 1; Kundeti §6 | Medvedev page 5 image; Kundeti lines 357–363 |
| BJJ report: Crochemore credited with Lyndon min/max-rotation argument in concluding remarks | BRICS lines 594–610 (acknowledgement inside §7 Concluding Remarks) |
| Collapsing §§2.2, 7.2 | section headings lines 236, 943 |

None of these bodies contains a reverse-complement forced-count rule, a phase-labelled layer parity, or an odd-core rule. That includes the Fici paper, which the contribution r3 reviewer had not seen. The credited package therefore stands as the contribution review defined it. This is project-relative and is not a priority claim.

Bibliography: WABI 2:1–2:13 and its DOI, CPM 15:1–15:11, the JLD and BJJ DOIs (via the WABI reference list), and Mucha's page range (via Fici) match the local primary text. The Collapsing LIPIcs metadata and Mucha's DOI rest on parent records, as `bibliography-audit.json` discloses.

## 6. Motivation examples and limits

- The W6/OPT7 example is limited to refuting a same-W symmetric connection. The text says it does not refute factor two or all equivariant methods. I recomputed OPT_RC = 7 by exhaustive search (witness `bbcbbcb`; 2 optimal words).
- The `{aaa,aab,abcaa,accc}` example is limited to arbitrary minimum-tie certificates. I recomputed OPT_RC = 10.
- In (abcacb)^ℤ, the unique lexmax rotation starts at 4. The length-7 palindromic (fixed) windows start at 0 and 3. The windows `cbabcac` and `cbabcacb` at start 4 are not fixed.
- I did not recompute W = 6, W = 12, or the tie certificates 11 and 9. Those values rest on the author verifier, the proof reviewer's `rc_counts.py`, and contribution round 1.
- §1.3 states that these finite certificates are not used in the proof.

## 7. Formal scope, diagnostics and AI attribution

Appendix A does not overstate the formal work. It describes 16 support theorems, says the main theorem is not formalized, and lists the formal O3–O7 limits. It distinguishes the 7 author controls from the 59 reviewer declarations, and it states the harness and trust limits.

Appendix A.2 labels the diagnostics as not proof. It discloses that zero multi-child flipped batches occurred in the reviewer model runs, and says the routing argument rests on the mathematics.

Appendix B separates the GPT-6 Astra author-side work from the Claude Opus 5.5 reviews (the dispatch records confirm the reviewer model). It claims no human refereeing. Its reading limits match `reading-provenance.json`.

## 8. Reproducibility and pages

- Two fresh builds from a copied source (Tectonic 0.17.0, `--only-cached --untrusted`, SOURCE_DATE_EPOCH = 1792195200, TZ = UTC) exited 0 and produced the frozen PDF byte for byte. The `.aux`/`.out` files equal the author's, the logs are identical across the two builds, and the source copy was unchanged.
- pdfinfo reports 17 pages, A4, 145648 bytes. All 15 fonts are embedded and subset. pdftotext shows no `??`.
- I rendered every page at 130 dpi with pdftoppm and read each image individually (`pages/`, hashes and notes in `pages/page-inspection.json`). There is no clipping, overfull text, unresolved reference or broken math.
- Three Underfull `\hbox` warnings exist that `build.py` does not flag and the author's page record does not mention (MR-O1).

## 9. Negative controls on the frozen packet

I wrote my own runner (`reproduction/scripts/author_controls.py`). It runs the author's `verify.py` on disposable copies in `/var/tmp`, under the final anchor. All 17 cases matched (`reproduction/author-packet-controls.json`), and the source tree digest was unchanged before and after.

- **Positive:** PASS.
- **Rejected as expected:**
  - wrong anchor and malformed anchor;
  - changed file, missing file and extra file;
  - extra empty directory and missing directory;
  - symlinked file, symlinked root and symlinked ancestor;
  - hardlinked existing file;
  - FIFO replacing a file and extra FIFO;
  - recomputed manifest checked against the old anchor.
- **Positive control:** the same recomputed manifest passes under its own new anchor. This confirms that integrity rests on the external anchor.

`/tmp` hit a per-user quota on the first attempt, so the controls were moved to `/var/tmp`.

## 10. Optional findings

- **MR-O1.** Three underfull lines: 01-scope.tex lines 41–47, and reference [1] on page 16, which is visibly stretched. They are unflagged by `build.py` and not recorded on the page-inspection record.
- **MR-O2.** `\path` labels break after the colon on page 2.
- **MR-O3.** In §6.1, "band joining each component costs at most 2(k−1)p" should say the block and its mirror together cost 2(k−1)p.
- **MR-O4.** WABI's formal copies are in §4.2. The current "especially Section 2 …" wording is acceptable, but naming §4.2 would be more exact.
- **MR-O5.** The in-packet controls used a pre-final anchor. This review supplies final-anchor controls, so no action is needed.

## 11. Seal

`MANIFEST.json` lists every file (bytes, sha256) and every directory in this directory except itself. `verify.py --anchor <sha256 of MANIFEST.json>` is read-only. It:

- checks the anchor format;
- checks that the root and its ancestors are real directories;
- checks that the manifest is a single-linked regular file;
- hashes the raw manifest before parsing it;
- requires an exact file and directory inventory;
- rejects symlinks, hardlinks, FIFOs and other nonregular nodes.

The anchor is supplied only in the handoff, not inside the manifest. Controls on this review packet ran after sealing, on copies, and are reported in the handoff.
