# Expanded corpus r69 — investigator handback

**No qualifying discovery and no Lean endpoint. Zero proposed credit. Campaign count remains 9/20 beyond the 39 prior results; only root may accept.** Investigation completed 1 November 2026, approximately 19:40–19:51 UTC. All new files are inside this assigned lane. No git, shared ledger/index edits, publication, upload, browser tab, external message, or child agent was used.

## Deliverables and coverage

* `results.json`: exactly 40 ID-keyed entries matching `reservation.json`, from 373606 through 374644. Each preserves the literal statement, chunk path and one-based line, chunk/raw-line/statement hashes, source receipt, recovered semantic scope, history assessment, review-depth limit, disposition and remaining obligation.
* `raw/<ID>.jsonl`: exact original bytes including terminating newline, not reserialized JSON.
* `sources/`: all 37 distinct assigned primary arXiv HTML bodies and derived text, plus selected later papers, two pinned registry manuscript introductions, public precoloring discussion, and live registry commit responses.
* `receipts/`: dated URL/status/actual-byte-hash receipts and bounded live web-search outputs. The one incorrect hot-spots source path returned 404; the corrected path was obtained from the complete path listing. No denied route was bypassed.
* `ROUTES.md`: sustained mathematical analysis for 373908, 374231 and 374390, distinguishing failed proof mechanisms from counterexamples.
* `scripts/` and `outputs/`: reproducible extraction, source reading, fetching, diagnostics, dispositions, validation, raw outputs and complete retained diagnostic run logs.
* `manifest.json` and `outputs/validation.json`: artifact hashes and successful exact-ID/raw-statement/receipt checks.

All 40 literal statements and targeted primary conjecture/definition material were reviewed. This is **not** a claim that every full paper or all cited proofs were read. Several difficult fields received primary-statement screening only, while material definition gaps remain explicitly parked. The strongest three routes received additional calculations and structural analysis. Eight entries are excluded from further discovery investment; 32 remain parked, including those three routes. No parked entry is called resolved.

## Findings that prevent false credit

**373686, non-isomorphic spanning trees:** the later Yan–Zhang paper arXiv:2609.30201 states the exact extremal theorem for every fixed d>=3. Its Theorem 1.1 and Proposition 5.1 imply the proposed n^(d-1) lower bound. The concluding proof was read; the deeper stability machinery was not independently audited.

**374000, hard-core variance:** the currently served version of the assigned primary paper has a changed title and proves both requested bounds in Theorem 1.3 and Corollary 1.4. The full covariance/extension-count proof was read. Reproving it in Lean would be known-result formalization.

**374321, Scott's odd induced subgraph bound:** the primary paper already gives a nine-vertex bipartite counterexample with maximum odd induced order four, with a finite case proof and an infinite disjoint-union construction. The universal statement is already refuted; its claw-free positive theorem is a different scope.

**373772, directed cycles:** Grzesik–Volec arXiv:2102.12830 Theorem 1.4 gives the sharp residue-sensitive thresholds and identifies failures of the older conjectured threshold. Merely observing that the assigned source still calls it open cannot make a new discovery.

**373848, relative Boone–Higman:** the trusted pinned OpenAI Boone–Higman theorem and the assigned primary paper's explicit Theorem C/5.1 and Lemma 5.2 give the direct existing bridge to the relative assertion. This is excluded as a routine consequence under the instructed upstream trust rule.

**373796:** exact-ID history found the earlier normalization/scaling exclusion in `root-nearline-r1/screening.md`; that route was stopped. **374305:** the displayed pullback-to-hyperkähler formulation has a diffeomorphism-invariance defect; exploiting it would be an ineligible wording correction.

The public precoloring discussion **does not** resolve 373805: its star/C4 counterexample takes k=chi'(G), whereas this reservation explicitly requires k<chi'(G). The current ETGC source for 374023 now lists seven operations, including PDS-complementation, rather than the record's six. Neither observation is promoted as an exact campaign solution.

## Sustained routes and remaining gaps

**373908 — median spectrum:** constructed the 26-vertex incidence graph of PG(2,3), verified the exact incidence identity B B^T=3I+J, and tested both degree-preserving switches and all single-edge deletions. No numerical violation among 400 switch sequences or 52 deletions. Disconnected-padding inertia and the source's quartic-moment argument were also analyzed. The missing ingredient is a genuine structural spectral gap outside the excluded incidence designs; the existing moment constraints alone allow the design distribution. Numerical spectra were not formalized or treated as proofs.

**374231 — odd edge coloring:** investigated the cubic parity obstruction, its failure after raising minimum degree, and the source's 27-vertex obstruction to extending its proof technique. All 13 tested odd circulants and that source graph have explicitly returned colorings whose vertex/color degrees were independently checked as zero or odd. Thus absence of the source's auxiliary T-join is not a conjecture counterexample. A universal recoloring/construction argument across three-vertex cuts is missing.

**374390 — BCH distance:** computed exact binary cyclic generators for 27 pairs 3<=m<=8, 1<=t<m; fully enumerated the 11 codes of dimension at most 20 and explicitly skipped the other 16. Every enumerated minimum matched the Bose formula. Beyond enumeration, inspected the source locator construction, subfield/splitting obstruction when t does not divide m, and the distinction between nominal and Bose distances. A general minimum-weight locator construction or a certified strict lower-bound counterexample remains missing. No parameter instance earns credit.

## Registry, history and access limits

Live `https://api.github.com/repos/openai/math/commits/HEAD` and `https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD` returned 200 at 19:40:18 UTC. Heads were respectively `4eaee87548250b2682affda7d05d947c05554bae` and `790d20daa36ba56dd2bd55777592ac36cf8a92ef`, matching the authoritative brief. No `/commits/main` call was made.

The byte-hashed complete inherited D5, Problems and OpenAI preprints lists were screened by ID and selected subject terms. No assigned ID path matched. This is path screening only, not proof-body or global novelty clearance. The Omega trees were inherited through the prior lane and compared using the brief's current-head attestation; this lane did not independently re-fetch every subtree or compare every intervening commit. The OpenAI Boone–Higman and strict smooth planar hot-spots theorem introductions were fetched at the live immutable commit and read. The latter has a smooth planar scope; it does not automatically clear every nonsmooth/higher-dimensional wording of 374311.

Exact word-boundary IDs and literal titles were searched in campaign Markdown, results and review files. Incidental substring matches were retained separately. This is not an audit of every binary/PDF/history artifact. No live MathDB/Palomar access was attempted after inherited access warnings. Web searches were bounded; title/abstract-only later leads are not treated as primary proof clearance. Unread cited bodies and full registry semantics remain limitations for every parked route.

## Reproduction and resource limits

Run `python scripts/extract.py`, `python scripts/read_sources.py`, and the fetching commands documented by `scripts/fetch.py`/supplementary scripts to recreate source material (live versions can change). Run diagnostics with `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 140s python scripts/diagnostics.py spectral` (or `odd`, `bch`). Then run `python scripts/dispositions.py` and `python scripts/validate.py`.

Diagnostic processes explicitly restrict affinity to two CPUs, CPU time to 120 seconds and address space to 6 GiB, with external 140-second timeouts. Final recorded maximum resident sizes were approximately 33 MiB, 112 MiB and 13 MiB for spectral, odd and BCH runs; each completed in under one second. SciPy reports that its `threads:1` option is passed through to HiGHS; CPU affinity independently enforces the two-CPU ceiling. Colorings are checked using integers after solving. No optimizer infeasibility is claimed as proof.

No Lean packet exists because no genuine literal endpoint was proved. Consequently there is no strict extracted rebuild, leanchecker run, or local-declaration axiom audit to report, and no upstream cache trust attestation is implied. Dependencies were not edited. All launched jobs finished before handback.
