# Reading limits, T337E contribution round 1

Bounded reading. Absence of a statement in what was read is not a worldwide novelty claim. Line ranges refer to the packet's authenticated text files (`fresh-analytic-discovery-r58/private/...`) unless stated otherwise.

## Author packet (all read in full)

`proof.md`, `original-scope.txt`, `checkpoint.md`, `source-map.md`, `contribution.md`, `reading-limits.md`, `081-history-reconciliation.md`, `337-working-interface.md`, `formal-plan.md`, `verify.py`, `controls.py`, `diagnostic.py`, all receipt JSON files. Parent `t337e-parent/sealed-preflight.json` and `t337e-parent/contribution-r1-dispatch.txt` read in full. The parallel proof reviewer's draft was not opened.

## Pinned source family (canonical blobs authenticated)

Sharp integral fillings in CAT(0) spaces (source337):

* Read in full: `01-introduction`, `03-radial` (including `prop:radial`, `prop:base`, `eq:base-cutoff-estimate`), `07-conclusion` (including `lem:opposite-average`), `08-classical`.
* Read in part: `06-chords` lines 440–507 (`rem:chord-sphere`); `05-minimizer` lines 370–409 (strictness in `prop:minimizer`).
* Statements only, bodies not re-read: `02` (`thm:current-background`, `prop:chart-mass`, `lem:euclidean-density`, `eq:extremizer`, `eq:normalization`), `04`.
* `rg` over all source337 sections found no equality or rigidity statement for the filling inequality.

Smooth Cartan–Hadamard companion (smooth337):

* Read: `01-introduction` lines 1–130 (`thm:equality`); `08-rigidity` in full (`eq:offset-sphere`, phase recovery, m≥3 spectral gap and barycentre).
* Not read: other smooth337 sections.

081 family: only through the packet's `081-history-reconciliation.md` and the parent preflight; no 081 body was read in this round.

## Primary literature

* Schulze, arXiv 1802.00226v3: lines 1–185 (Theorems 1.1–1.4) and 1120–1359 (§6 equality case). Middle sections not read.
* Stadler, arXiv 2212.07100v1: lines 1–90, 236–315 (§2.6 parallel sets), 760–999 (Appendix A: Proposition A.1, Sublemmas A.2–A.3, Corollary A.4).
* Basso–Creutz–Soultanis, arXiv 2209.12545v3: lines 1–230 and 655–909 (§§4–5, including the full proof of Theorem 1.2). §3 not read.
* Druţu–Lang–Papasoglu–Stadler, arXiv 2502.03389v1 (retrieved by this reviewer; `private/dlps2502.pdf`, SHA256 `e8d06055f51743e354074bbb0bfbeeaf059ce8cf51e6f46925d2dcda97d2dddb`): text lines 30–154, 615–664, and Proposition 7.1 with proof.
* TauCeti roadmap PR 829 (`private/roadmap829.html`): skimmed; concerns Euclidean formalization only.
* Stadler, arXiv 2609.33633 (27 Sep 2026): abstract page only. Non-sharp linear filling counterexamples; irrelevant to equality.

## Project history

* Read in full: `frontier/iterations/i286-quantitative-cartan-hadamard.md` and its parent disposition.
* Read in part: `frontier/iterations/i91-finite-cat0-obstruction.md` (opening and lines 290–312).
* Hit lines only: r34 `report.md` and `second-history-screen.json`, r51 `reading-limits.md`, `frontier/reviews/i96-finite-cat0-obstruction-novelty-r3.md` (uses source337 07 for a finite obstruction; TECHNICAL; not an equality target), t197h review and disposition (different pinned CAT(0) group manuscript), `frontier/NEW-TEN-2026-10-14.md` (T337E dispatch entry and T197H entry).

## Not read

* Lytchak 2004 (Theorem 1.6, §7.7): the tangent-cone realization step is taken from the author's citation and its identical use in Stadler Sublemma A.2.
* Almgren 1986: the Euclidean equality case is taken from its statement as quoted in Schulze Theorem 1.1 and the source337 introduction.
* Del Nin–Perales (JMAA 2023, mass-preserving 1-Lipschitz maps from integral current spaces): seen as a search hit only.
* Bridson–Haefliger II.2 (flat strip, parallel sets): used from standard knowledge and Stadler §2.6.
* source337 `02`, `04` bodies; BCS §3; smooth337 sections other than 01 and 08.

None of the unread items could move the verdict to SUBSTANTIAL. They could only strengthen a DUPLICATE sub-case or confirm a step already classed as classical.
