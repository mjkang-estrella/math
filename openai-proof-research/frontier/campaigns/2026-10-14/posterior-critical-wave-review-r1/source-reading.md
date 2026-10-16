# Reviewer reading and retrieval log

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Review round 1,
read 2026-10-16. Only the extents below are claimed as read. Byte
authentication is recorded separately and is not reading or validity.

## Instructions and context (read in full)

* `inputs/parent/review-r1-brief.txt`, 905 lines: active review
  instructions, original-brief identity, parent disposition and P1–P6. Its
  embedded author files were confirmed to contain the authenticated author
  files verbatim (substring check), and those were read in full.
* `inputs/parent/fresh-r14-brief.txt`, 643 lines, SHA256 97d8e33d…aa79: the
  complete original discovery brief, including the historical T4, LC and
  r13 appendices. Historical instructions are context only.
* `inputs/context/AGENTS.md`, `inputs/context/upstream.json`: all.
* `inputs/context/NEW-TEN-2026-10-14.snapshot.md`: internal snapshot of the
  mutable ledger at review start, used only to confirm the 4/10 count and
  exclusions. Future ledger changes are not bound by this package.
* Parent files r14-disposition.md, r14-terminal.json, r14-verification.json,
  next-tasks.json, review-r1-launch.json: all. `verify_frozen_r14.py` was
  read as text (stored as `.py.txt`) and not executed.

## Author package (authenticated first; see review.md Section 1)

Read in full: original-scope.md, candidate.md (474 lines), checkpoints.md,
screening-before-freeze.md, source-contracts.md, source-reading.md,
operation-comparison.md, status.json, freeze-record.json, seal.json,
manifest.json, README.md, verify.py, guard.py. The author's retained source
and primary copies were used as byte-identified reading copies; the author's
reading claims were not inherited.

## Pinned source P, family236 (commit fd4aeeb2…eeeb)

Copies in `inputs/pinned/` are byte-identical to the author's authenticated
copies; `verify.py` recomputes their Git blob identities.

* `02-posterior-fields.tex` 1–282 (all): free law, likelihood, cavity and
  site recursions, field bounds, proof, exhaustion and versions.
* `03-critical-information.tex` 1–300: fusion lemma, critical information
  lemma and proof, root/neighbor spin tilts and proof, start of attenuation.
* `04-innovations.tex` 1–115 and 460–619: proposition and filtration
  interfaces; continuity, component-local versions and augmentation
  identification (the component-filtration statement at 589–603).
* `08-critical-comparison.tex` 1–205: setting, `lem:critical-tail` and its
  proof.
* `01-introduction.tex` 1–70: main statement and setting.
* Duplicate-statement screen of the pinned family: grep of all 15 author
  retained pinned/companion blobs for Gaussian/wave/CLT/invariance/functional
  terms, and listing of theorem headers in 05–07 (`prop:path-variance`,
  `lem:marginal-spectrum`, `lem:cut-continuation`, `prop:path-average`,
  `prop:weighted-paths`). Sections 05–07 bodies were not read; they are not
  PCW premises.

## External primary bodies

Author-retrieved copies (in the author package `inputs/primary/`, byte
identity in the author manifest and reviewer before-receipt):

* Yu–Polyanskiy, *Broadcasting on Trees Near Criticality: Perturbation
  Theory* (`near-critical.txt`): all 480 lines, including Theorem 1,
  Remarks 1–3, Lemmas 1–4 and proofs, (21) and the MGF normal-family proof.
* Yu–Polyanskiy, arXiv:2211.15242v2 (`cavity.txt`): lines 88–147 (BP with
  survey, Theorem 1, cited Gaussian limit) and 505–574 (comparison of
  methods, Theorems 15–16, proof of Theorem 15). Other parts not read.
* Nam–Sly–Zhang, arXiv:2012.09484v2 (`nsz.txt`): lines 1–60 (abstract,
  introduction) and 187–310 (§2.1–2.2, Lemma 2.1 with proof, Propositions
  2.2–2.3 statements). Later estimates not read.
* Elon, arXiv:0907.5065v2 (`elon.txt`): lines 1–325 (Theorem 1.1,
  Lemmas 2.1–2.2 with proofs and covariance formula). The value of the
  covariance at lambda=2 sqrt(b) was recomputed and equals phi_d.

Reviewer-retrieved copies (`inputs/primary/`, fetched with curl from arXiv
PDF endpoints, converted once with `pdftotext -layout`; no downloaded code
run):

| file | source | bytes | read extent |
|---|---|---|---|
| jklm.pdf/.txt | Jain–Koehler–Liu–Mossel, *Accuracy-memory tradeoffs and phase transitions in belief propagation*, COLT 2019, https://arxiv.org/pdf/1905.10031v1 | 484843 | txt 255–300 (Thm 3, Cor 4), 475–665 (proof plan, Lemma 5, decoupled S-bar vs S-hat), 1584–1693 (Lemma 23 and proof), 2257–2303 (Appendix E, Lemma 29) |
| whitt.pdf/.txt | Whitt, *Proofs of the martingale FCLT*, Probability Surveys, https://arxiv.org/pdf/0712.1929v1 | 400677 | txt 95–279 (Theorem 2.1 multidimensional martingale FCLT, Lemma 2.1, proof outline) |
| janson-mossel.pdf/.txt | Janson–Mossel, *Robust reconstruction on trees is determined by the second eigenvalue*, Ann. Probab. 32 (2004), https://arxiv.org/pdf/math/0406447v2 | 265209 | txt 160–219 (Theorem 1.2, Proposition 1.3), 495–614 (Lemmas 2.7–2.8, linearization near the trivial measure) |

Standard textbook facts used without a retained body: Doob's L^p
inequality, L^4 Burkholder–Davis–Gundy, Dambis–Dubins–Schwarz, Brownian
reflection and modulus of continuity, Kolmogorov extension, and the
Ethier–Kurtz martingale FCLT (cited for identification only; Whitt's
survey is the retained body for that comparison).

## Searches

Bounded web searches: "Jain Koehler Liu Mossel belief propagation near
critical Gaussian"; "martingale functional central limit theorem Whitt
proofs"; "posterior Gaussian process tree Ising Brownian observations
critical"; "Janson Mossel robust reconstruction second eigenvalue";
"near-critical broadcasting tree survey Gaussian". Search results and
snippets are not evidence; only the bodies above are. No exhaustive
priority search is claimed.

## Executed work

Author guard with external anchor and controls (after reading it); curl
downloads and pdftotext; hashing; this package's verifier and controls.
sympy was unavailable, so no symbolic diagnostic was run; all algebra in
review.md was done by hand. No numerical experiment, nested agent,
staging, commit, upload or external message.
