# Reading limits, T286F contribution round 1

Bounded reading. Absence of a statement in what was read is not a worldwide novelty claim. Packet paths are relative to `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r39/`. Line ranges refer to the packet's authenticated text files unless stated otherwise.

## Author packet

Read in full: `candidate286f.md`, `scope286f.md`, `scope286f-freeze.json`, `checkpoint.md`, `source-and-credit286f.md`, `reading-limits.md`, `kernel-proof286f.md`, `work286.md`, `verify.py`, `control-tests.py`. Read in part: `formal-interfaces286f.md` (head only). Not read: `308-*.md` (family308 side work, not part of T286F), `integrity.md` beyond its role in the manifest.

Parent `t286f-parent/`: contribution dispatch, `review-dispatch-r1.json` and `sealed-preflight.json` read. The parallel proof reviewer's directory was not opened.

## Pinned source family 286 (canonical blobs authenticated by the author verifier and by `cmp` of the tree)

*The arithmetic category and stable recovery of lattice factors* (`private/source286/preprints/The-arithmetic-category-and-stable-recovery-of-lattice-factors-September-23-2026/build/sections/`):

* `01-introduction.tex`: read in full (`def:class`, `thm:stable`, `thm:endpoints`, `thm:correspondences`, history crediting Vaes 2008 and Donvil–Vaes).
* `03-calculus.tex`: lines 350–791 read (`thm:calculus-hom`, regrouping/permutation remark, conjugate transport, `prop:calculus-fusion`, `eq:calculus-double-coset-fusion` with `q_m`, associativity). Lines 1–349 consulted only for labels (`lem:calculus-germ-test`, `lem:calculus-induction`, `lem:calculus-graph-model`, `eq:calculus-regrouping`, `eq:calculus-representative-change`).
* `04-endpoints.tex`: lines 1–385 read (`lem:endpoints-extension`, `lem:endpoints-grading`, `lem:endpoints-bounded-grades`, `lem:endpoints-minimal-corner`, `prop:endpoints-corner-constraints`). Lines 386–524 not read.
* `05-examples.tex`: read in full.
* `02-models.tex`: not read.

*Arithmeticity of twisted finite correspondences for lattices over local fields*: `build/sections/00-introduction.tex` lines 1–145 (`def:class`, `thm:arithmetic-exhaustion`). Geometric sections 01–11 not read (stipulated).

`rg` over every section of both manuscripts: no fusion-subcategory, group-theoretical, Morita, Q-system or finite-depth subfactor statement.

## Primary bodies retained in the author packet (`private/primary/`)

* `Vaes2008.txt`: lines 120–519 (introduction, Thm 2.2, extended Hecke fusion algebra, Thm 2.8) and 1858–2057 (Defs 6.6–6.8, Thm 6.9 with proof, start of Prop 6.10).
* `EGNO.txt`: lines 16870–17029 (Def 9.7.1, Examples 9.7.2/9.7.4, Rem 9.7.6, Prop 9.7.9 with proof). Chapter 7 propositions cited by the author were not re-read.
* `Hamburg-Hecke.txt` (Gödicke dissertation): lines 1018–1227 (categorified Hecke algebra, Props 2.4–2.5, Rem 2.5, Def 2.4, Cor 2.6). Cor 11.4 and FGJS22 Prop 4.9 not read.
* `Izumi-3n.txt`: printed pp. 473–474 only.
* `DonvilVaes2025v3.html`: §6.3 extracted to scratch text (`/var/tmp/t286f-contrib-r1.rtCc0g/ext/DV.txt`, SHA256 `ff9c37a8…`, derived from the authenticated packet copy, not retained here), lines 885–994: Prop 6.5 with full proof, Thm 6.6, Lemmas 6.7–6.9.
* `BKLR2015`, `CKLW`, `CM`, `HT`, `GTalgebras2023`, Bhatt/Wuthrich/Miyamoto pages: not read for this gate (BKLR is credited by the author only for standard Q-system identities; the others serve family308 or history).

## External bodies retrieved in this round (`private/`, git-ignored, bound by `search-log.json` and `verify.py`)

* Arano–Vaes, arXiv:1602.03047 (34 pp.): text lines 20–349 (introduction, Hecke C\*-tensor category `C(K<G)`, `Rep K` as a full subcategory, independence of K up to Morita equivalence, hyperfinite realization). The remainder was not read. No finite-subcategory group-theoretical statement in the read range.
* Deprez–Vaes, JNCG 5 (2011) 523–545, Lirias author copy (19 pp.): §1 and §2 (text lines 1–600; Thm 1.2, Cor 1.4/1.5, Lemmas 2.1–2.4, full proof of Thm 1.2 including line 564), §4 (lines 783–962; Hecke bicategory with 2-cocycles, Thm 4.2). §3 (lines 601–782, concrete index computations) not read.
* Falguières–Raum, arXiv:1112.4088 (30 pp.): introduction, text lines 55–94 only.
* Müger, arXiv:math/0111204 (59 pp.): `grep` for "group-theoretical" and "Hecke" only (no hits); not read otherwise.
* Natale, arXiv:1808.09581: abstract page only (weakly group-theoretical extensions `Rep G → C → D`); not used for the verdict.

All text files are byte-identical replays of `pdftotext -layout` (poppler 26.01.0) on the stored PDFs.

## Not done

No search of MathSciNet/zbMATH. No reading of Popa–Vaes, Bisch–Haagerup or Ostrik module-category papers beyond what EGNO restates. No author contact. The verdict would only move toward DUPLICATE if an unread body already states the finite-subcategory reduction for infinite twisted Hecke correspondence categories.
