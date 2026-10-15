# Reading record and provenance — kinetic window (Factory/Opus fallback)

Date: 2026-10-14. Upstream: `openai/math` at pin
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (from `sources/upstream.json`).
Upstream theorem truth is stipulated by the user. Nothing below audits it.

## 1. Source H and how it was obtained

H is the preprint directory
`preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/`.

No file was fetched in this run. The copies in
`../kinetic-window-discovery/fetched-H/` were reused read-only. That directory
has no fetch log of its own. Its contents were therefore authenticated by
content, not by who fetched them: for every file, the git blob SHA1 computed
locally (`git hash-object --no-filters`) equals the `sha` recorded for the same
path in `sources/preprints-tree.json`, which is the pinned tree listing. The
nine files other than `main.tex` also match the hashes in
`frontier/experiments/i340_kinetic_path_fluctuations/input-authentication.json`
(that file does not list `main.tex`).

Pinned raw URL pattern:
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/<path>`

| `<path>` | git blob SHA1 | sha256 | bytes | lines | Read in this run |
|---|---|---|---|---|---|
| `sections/01-introduction.tex` | `18a097780185a88aa5b57470c4d38cf18ac8b948` | `f64b52941054e73c5a9e80ed7698c6a2d0a5d7f6894decd8c9dbb8fcd9d4c2a8` | 11368 | 242 | in full |
| `sections/02-initial-target.tex` | `1050ba9ab12b849d5f13c9394145c6de7bd4432d` | `51fad6beefe3041c56ea2686776dbfdedf8522120762f4aaef019947fe902396` | 23065 | 544 | grep only: statements of `prop:initial` (line 38) and `eq:initial-N-moments` (line 48) |
| `sections/03-dhm-inputs.tex` | `ffa665888b0880d2db70d38e5224930e8220825d` | `a2506a516767704d4d3630e65395ed7b9481fbcbddff912ad38ba2441e5c1cbf` | 20583 | 397 | in full |
| `sections/04-cluster-expansion.tex` | `87d6cdc96897bf2ee2a3f26fdd16c9129a36acef` | `5f824af314132999e830425354a43a273d2e17e14bf46d02a4d254917c8f8d47` | 39676 | 781 | in full |
| `sections/05-cutoff.tex` | `81f66d308c4b56ec6c590b957812860ad6cb0a8d` | `e5380f7a81c4f32ce23ebf3ad62aee4f23c4530d342da2198cd2b9602ecfac4e` | 52765 | 1186 | grep only: `prop:cutoff` statement (line 14; $\eta=1/20$, every fixed $L\ge L_0$) |
| `sections/06-sharp-asymptotics.tex` | `dfa4a25d5099bd82301c83bb31c612f0bfae4788` | `32a5a00ce410873a30fbed113b0b1ec56a80da5b6bc28664ae19a73637282883` | 47771 | 946 | in full |
| `sections/07-gaussian-limit.tex` | `abc670cb5738eeae520ac52863f4a87bd2a2994a` | `9cf6ab1d1c78ab4203a403bfc09331779c2b9b029280f1751009b0ac4faf99e4` | 20846 | 449 | lines 1–90 (contains `eq:limit-mark-update`, line 18); grep with context for `prop:cumulant-clt` (line 363) and `eq:limit-factorial-ordinary` (line 381) |
| `sections/08-transfer.tex` | `82268938b3f06db181df356ec3038b87a5bfb23a` | `3efa338da518fd1141222a800e9ef45b3a3b998145d3aa39e725abe35b240136` | 3357 | 69 | grep only: `lem:center-transfer` (line 14) |
| `main.tex` | `fd0e2981390c55f076c43103e837f0beb3701e59` | `4f84d56fd4dcb78bb2f776063969c097279feaa19a74e95a63be2613d90e53af` | 3819 | 92 | hash only |
| `references.bib` | `5e0a24b2a91635abe1db3c484685ea158a583bd6` | `6c423a9ebddaa027e88a9e34ebdcb49188642d22219b9b5d8049d9de663d4a6c` | 5705 | — | hash only |

Consequences of the partial reading:

- §02, §05 and §08 are used only through the displayed statements of
  `prop:initial`/`eq:initial-N-moments`, `prop:cutoff` and
  `lem:center-transfer`. These uses are inherited from I340 §3 (exact-centering
  transfer), which the parent already verified. The model `eq:grand-canonical`
  is in §01, read in full.
- §07 is used through `eq:limit-mark-update` (two-pulse scalar marks) and
  `eq:limit-factorial-ordinary` (factorial-to-ordinary cumulants). Their
  statements were read; the rest of §07 (the Gaussian identification) is used
  only through `thm:main` in §01.
- The new step, Lemma W, depends on §03 and §06, which were read in full, and
  on the one-slab identity in §04, which was read in full.

## 2. Project files read (read-only)

- `AGENTS.md`, `sources/upstream.json`, `sources/preprints-tree.json` (hash
  lookup only).
- `frontier/experiments/i340_kinetic_path_fluctuations/analysis.md`,
  `reading-and-failures.md`, `input-authentication.json`.
- `frontier/iterations/i340-kinetic-path-fluctuations.md` (the I340 iteration
  note).
- `frontier/campaigns/2026-10-14/NEW-TEN-2026-10-14.md`. This shared file
  changed during the run (it now records 1/10 accepted and a line saying
  Factory/Opus is investigating I340). It was only read and was not edited.

## 3. External literature

None was opened in this run. Every statement about BGSS (arXiv:2008.10403v2,
arXiv:2201.04514v1) or DHM (arXiv:2408.07818v3) in `candidate.md` and
`exclusions-and-failures.md` repeats I340's recorded reading. In particular,
the novelty of whole-history time-shift averaging (Lemma W) relative to the
BGSS cumulant papers was **not** checked.

## 4. Numerical checks (illustration, not proof)

Files: `checks/shift_checks.py` (standard-library Python 3, fixed seed
`20261014`, toy diameter $\varepsilon=0.35$) and its output
`checks/shift_checks.json`.

| Check | What it tests | Result |
|---|---|---|
| Covariance | Random formal chronological charts with up to five lines, including determined redundant contacts. Shift all merger times by $\theta$ and move $X$ by $-\theta v_{\rm rep}$; compare event times and velocities. | 400,000 trials, 1,709 realized redundant contacts, 0 existence mismatches, max error $1.07\times10^{-12}$ |
| Minkowski volume | $\operatorname{vol}(S-[0,\Theta]\mathbf 1)=\frac{\tau^a}{a!}(1+a\Theta/\tau)$ by Monte Carlo, $a\le5$ | agreement within Monte Carlo noise; largest relative deviation 2.7% at $a=5$ |
| Averaging toy | Three-line cycle (two mergers and one redundant contact). Compares $\mathrm{Leb}(D)P_D(t_*\in J)$ with the Lemma W right side $(|J|/\Theta)\mathrm{Leb}(D_\Theta)P_{D_\Theta}(t_*\text{ exists})$ over 33 windows | 150,000 samples; max ratio left/right 0.487 (never above 1) |

These checks can catch an algebra slip in the shift map or the volume formula.
They do not test H's estimates, the summation over diagrams, Lemma E′, or any
limit statement. The proofs in `candidate.md` do not depend on them.

Reproduction: `python3 checks/shift_checks.py` from this directory rewrites
`checks/shift_checks.json`. A seeded rerun in a temporary copy is recorded in
`provenance.json`.
