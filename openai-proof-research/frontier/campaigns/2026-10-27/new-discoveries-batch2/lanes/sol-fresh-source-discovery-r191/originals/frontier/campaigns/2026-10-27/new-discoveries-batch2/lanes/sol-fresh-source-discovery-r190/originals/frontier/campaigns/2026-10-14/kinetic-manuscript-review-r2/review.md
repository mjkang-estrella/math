# Focused manuscript gate — corrected kinetic edition, round 2

**Verdict: PASS** for the corrected standalone edition in `kinetic-manuscript-consolidation/`, relative to the full original theorem and relative to the stipulated truth of H at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

All seven round-1 requests (N1–N7) are resolved in the actual bytes. The two new arguments (fixed-time collision nullness and supremum tightness) are mathematically sound. The diff changes no hypothesis, quantifier or conclusion of the theorem, and it removes none of the earlier proof repairs or formalization limits. **No mathematical repair is required.** Section 4 lists six editorial suggestions; none of them reopens a proof claim.

This review covers proof and presentation only. It makes no acceptance, count, novelty or priority decision, and it is not a Lean certificate. The round-1 PASS and the author's and parent's QA were read as context, not used as premises.

## 1. Authentication

All brief hashes match the bytes on disk. `input-authentication.json` lists all 71 files read or executed, with length and SHA256.

| Object | Bytes | SHA256 |
|---|---|---|
| Frozen original `kinetic-manuscript/main.tex` | 61392 | `969c35d11d8242c35117b77233d2612761ac56bc231f7365acd2172ad6f08d29` |
| Frozen original PDF | 186051 | `c7f2c4533c58d15157445b4b19044c2c1b324ce7972ea106ea158e4601412565` |
| Corrected `main.tex` | 64053 | `f2548882cf47aa4259c68b43ea38d755c395b47008300783856788ab5ef6fd38` |
| Corrected `output/pdf/main.pdf` (19 pages) | 190507 | `08a092590559fa81c1d2c759e06efb9a03b1e7b6ede1d708ace731cc0f2028dc` |
| `inputs.json` | 20512 | `66e05660c2f9636989f22ab7587fdc05dab27af73d1707821bc910f43fd0cf87` |
| `outputs.json` | 8873 | `a299015528841be2324fc210ae59c3c48028c4c7448bcd8762a3e5502dee1536` |
| `original-to-consolidated.diff` | 14231 | `fb97e6c310d009d2da95c3b9fac3c425ed90e422179ff9ad4516010d61915a99` |
| Round-1 `review.md` | 19651 | `be96cc4ca94c3e7e1d46b908768b29008ae886a4b84309cc1d136a69115f54e1` |
| Round-1 `outputs.json` | 1412 | `82ea15f91395b9ccd205c6a767323ee4834da83411e944138be16cd74b59fb1b` |
| `references.tex` (unchanged) | 1898 | `3797dd451cf0f48db9bde382ae8ef363360d10257569af0105ab257e2e0d8e09` |

**The diff is exact.** I applied the supplied diff (16 hunks) with `git apply` to a copy of the frozen original in `/tmp/kmr2-patch`. The result is byte-identical to the corrected `main.tex` (`f2548882…`). My own `diff -u` differs from the supplied file only in hunk alignment. So the diff is the complete set of TeX changes, and everything outside it is the round-1-reviewed text.

**Manifests.** I checked these independently of the package verifier:
- all 107 `inputs.json` records and all 57 `outputs.json` records match the bytes on disk;
- the only unlisted file is `outputs.json` itself, which is by design;
- 12 output records are byte-identical to records of the original's 46-record manifest, and the rest are listed as changed or new.

## 2. N1–N7 dispositions

| Item | Disposition | Location in corrected `main.tex` |
|---|---|---|
| N1 collision convention | **Resolved.** The new argument is sound (§3.1). | 105–118 |
| N2 H shorthand and sections | **Resolved.** The mapping was verified against the pinned `main.tex` (§3.2). | 191–217 |
| N3 public credit, I340, process prose | **Resolved.** One credit suggestion remains (E5). | 1177–1180, 1273–1279 |
| N4 notation | **Resolved.** One pre-existing overload remains (E4). | 410–417, 589, 676, 765, 801–817, 883–887, 1059–1079 |
| N5 record-bound dependence | **Resolved.** One precision note (E2). | 336–362 |
| N6 pulse wording | **Resolved.** | 256–257 |
| N7 supremum tightness | **Resolved.** The new argument is sound (§3.3). One typo (E3). | 1155–1174 |

The round-1 N2 suggestion ("H0k means Section k") was wrong. The author checked the real inclusion order and correctly did not follow it (§3.2).

## 3. Independent checks of the changed mathematics

### 3.1 N1: a collision at a fixed time has probability zero (105–118)

The paper no longer attributes the convention to H. H01:105–109 cites only the almost-everywhere flow of DHM Prop. 1.2.

I checked the argument against the sealed local DHM v3 (`dhm_v3.pdf`/`.txt`, which match `artifact-seal.json`):
- DHM Def. 1.1 uses the closed domain D_N (|x_i−x_j| ≥ ε) with **left**-continuous velocities. The manuscript's right-continuous choice is therefore correctly presented as its own convention.
- DHM Prop. 1.2(3) states that the flow maps are measure-preserving diffeomorphisms of D_N minus a null set Z (proof via Alexander). This supplies exactly the measure preservation used at line 113.

The argument runs as follows:
1. For fixed N ≥ 2 the law has a Lebesgue density on D_N^ε.
2. Contact configurations lie on finitely many surfaces |x_i−x_j|=ε, which are Lebesgue-null.
3. Their preimage under a measure-preserving map, outside Z, is null.
4. Summing over countably many N, with N=0,1 trivial, gives the claim.

This is correct.

The same conclusion holds for the auxiliary pasted dynamics. DHM Prop. 4.5(4) gives L¹ preservation for the truncated dynamics, and through the pushforward definition (3.4) that dynamics is non-singular. Changing the convention at a null set of times therefore leaves every fixed-time input from H unchanged, as line 117 says.

### 3.2 N2: section mapping (191–217)

I checked the cached H files by git blob SHA1 against `sources/preprints-tree.json`: all eight sections, the H `main.tex` (blob `fd0e2981…`, 3819 B) and `references.bib` match the pin.

H `main.tex` lines 82–89 include the files in the order 01, 02, 03, 04, 06, 07, 05, 08. Each file contains exactly one `\section`, and there is no appendix or counter reset. Hence:
- H05 is Section 7;
- H06 is Section 5;
- H07 is Section 6;
- every other H0k is Section k.

The section titles printed in the paper match the `\section` arguments exactly.

All typewriter labels cited in the changed text exist in the stated files: H01 `ass:kinetic`, `thm:main`; H02 `prop:initial`, `lem:target-propagator`; H03 `lem:kinetic-envelopes`; H04 `lem:autonomous-partition`, `thm:marked-expansion`, `lem:diagram-labels`; H05 `prop:cutoff`; H06 `lem:sharp-merger-coordinates`; H07 `eq:limit-factorial-ordinary`.

### 3.3 N7: supremum tightness (1155–1174)

The checks:
- **Double limit.** The double limit at 1156–1160 follows from the preceding dyadic bound: first let ε→0, then k₀→∞.
- **Deterministic bound.** Cover [0,T] by ⌈T/u⌉ intervals of length at most u. Then sup_t|Y_t| ≤ |Y_0| + ⌈T/u⌉·w(Y,u), with w the continuity modulus, as displayed.
- **Choice of u.** For a given tolerance, the double limit fixes a u with limsup_ε P(w(Y^ε,u)>1) below that tolerance. Initial tightness then bounds |Y_0^ε|. So lim_A limsup_ε P(sup|Y^ε|>A)=0.
- **Criterion.** Together with the modulus limit, this gives both hypotheses of Jacod–Shiryaev Prop. VI.3.26.

No moment assumption changed. The argument is sound.

### 3.4 N5: record-bound dependence (336–362)

H04:412–425 defines m as a bound on **both** the number of pulses and the number of labels carrying records. `eq:bounded-crossing-factorials` (H04:500–724) gives constants C_{K,h,m,L}. The coarse tail in `thm:marked-expansion` has the form C_{h,m} ε^{−C_*h−C_m+c_*K/2}.

The corrected `eq:factorials` and `eq:coarse` now carry r_rec, which is mapped to H04's m and kept distinct from the manuscript's birth-line count m. That is correct. The text describes r_rec only as a bound on the record list (line 336); see E2.

### 3.5 N4: notation (whole file searched)

- No bare M remains.
- d occurs only as the test dimension (159–165, 1066, 1248).
- The renames are complete: δ_p (589, 676); ν_i (801–807); γ_K (410, 765, 817); q_tail (415–417, 883–887); and, in §7, h for block size and j for factorial-moment order, with p only the particle index.
- The renamed exponent condition stays consistent: since q_tail > q+2j+2, we have q_tail − 2 > q.
- The E3 separations from round 1 (V, b, q/P, η₀/η, θ/ϑ) are intact.

### 3.6 N3: credits (1177–1180, 1273–1279)

`provenance.md` and `source-map.md` cite `frontier/experiments/i340_kinetic_path_fluctuations/analysis.md` §§2–3 and `frontier/iterations/i340-parent-path-transfer.md`. I read both. Their content matches the reproduced Gaussian-continuity and uniform exact-centering arguments.

"I340" and the PASS/SUBSTANTIAL prose are gone from the paper. Page 19 now states "No worldwide-priority claim is made" and makes no full-Lean claim.

### 3.7 Scope and earlier repairs preserved

I read every hunk of the diff in its surrounding context. None of them touches:
- the theorem statement, `eq:law` (including N=0), μ=ε⁻², the unsmoothed whole-space deterministic flow, the full supplied [0,T], exact microscopic centering, finite C_c^∞ test lists, or the J1 + C-tightness conclusion;
- the uniform-topology disclaimer.

The proof-r1 repairs and the E1–E7 items remain in place:
- chronology Q and structural O-ties;
- all-line energy and the fixed Gaussian budget with L chosen before K;
- the decorated kernel and component inversion;
- the exact Count remainder with its explicit weakening;
- the 1/440 transfer exponent.

The Lean paragraph (page 19) still describes exactly nine scoped support declarations and lists the same exclusions. `references.tex` is byte-unchanged.

## 4. Editorial suggestions (non-blocking; no mathematical repair required)

- **E1 — source for measure preservation (113–114).** Cite DHM Prop. 1.2(3) (Alexander) for the measure-preserving flow. Optionally note that nullness for the auxiliary pasted dynamics follows from DHM Prop. 4.5(4) (via H03).
- **E2 — r_rec bounds pulses too (336, 361).** H04's m bounds both the pulse count and the record-carrying labels. Write "a pulse list and a record list each bounded in number by r_rec". This is harmless here because pulse lists are fixed and Prop. 5.1 uses exactly two pulses.
- **E3 — typo (1162).** "partition $[0,t]$" should be "partition $[0,T]$".
- **E4 — δ overload (pre-existing).** δ denotes the Dirac delta, the offsets δ_p (§4) and δ=t−s (§5). Also, δ_p is used at 589/676 without a definition, as d_p was in the original; it is presumably x_p^ξ(b_p)−X. A one-line definition would help.
- **E5 — credit H08 (1177–1180).** The uniform exact-centering transfer repeats H08 `lem:center-transfer` (same Hölder step, p>(1+η)/η), and that lemma is never cited. Cite it, and name the uniform-in-time extension as the inherited part. This is pre-existing, not introduced by the diff.
- **E6 — package documentation.**
  - The antecedent notes credited in `provenance.md` are unpublished project files, so a public reader cannot follow them.
  - `response-to-review.md` (N4) says "lines 884-416"; it should say 883–887 / 415–417.

## 5. Support checks (disposable copies only)

All scripts ran on `/tmp/kmr2-uWUL`, a copy built from the 107 inputs, the H files and `kinetic-repair-r1/checks`. Nothing ran in a frozen directory.

| Check | Result |
|---|---|
| `verify_outputs.py` | PASS, 57 files |
| `verify.py` | PASS, 213 checks, 107 inputs, 25 claim groups, 19 pages |
| `verify_sources.py` | PASS, 10 files |
| `validation.json` and the three `checks/*.json` receipts | byte-identical to the frozen ones |

**Rebuild.** Tectonic rebuilt the PDF in `/tmp/kmr2-build-wztl`:
- the PDF bytes differ only in metadata;
- `qa/main.txt` is text-identical;
- all 19 renders are byte-identical to `qa/page-*.png`;
- the log has 0 warnings and 0 bad boxes.

These are finite structural checks, not mathematical evidence.

**Independent rendering.** I rendered the frozen corrected PDF myself at 105 dpi (`/tmp/kmr2-render-cGhz`):
- all 19 pages are byte-identical to the package PNGs, and all fonts are embedded;
- the title is "Functional hard-sphere fluctuations on a regular Boltzmann lifespan", the author is Myeongjin Kang, and there are 19 pages.

A per-page text comparison against the original shows page 1 unchanged and pages 2–19 changed, mostly by reflow. Every substantive change is on one of these pages:

| Page | Change |
|---|---|
| 2 | N1 |
| 3 | section table |
| 4 | N6, r_rec |
| 6, 13 | q_tail |
| 9–10 | δ_p |
| 6, 11, 12 | γ_K |
| 12 | ν_i |
| 16 | root cardinality |
| 17 | N7 |
| 17–19 | credits |
| 19 | no-priority statement |

I viewed pages 2, 3, 4, 5, 6, 10, 12, 13, 16, 17, 18 and 19 at full resolution. There is no clipping, overlap, broken equation or unresolved reference.

## 6. Read extents

- **Corrected `main.tex`:** lines 80–530, 529–928 and 1028–1309 in full, plus targeted searches across the whole file for every renamed symbol and label.
- **Diff:** read in full (all 16 hunks).
- **Original `main.tex`:** read at every hunk location for comparison.
- **Package documents read:** `response-to-review.md`, `provenance.md`, `source-map.md`, `source-sections.json`, `source-H.json`, `build.py`, `verify*.py`, `inputs.json`, `outputs.json`.
- **H (pinned cache):**
  - `main.tex` lines 82–89;
  - the `\section` line of all eight files;
  - H01:92–121;
  - H04:412–425 and 500–724;
  - label searches in H01–H08;
  - H08 `lem:center-transfer`.
- **DHM v3:** Def. 1.1, Prop. 1.2, equation (3.4) and Prop. 4.5.
- **Antecedent notes:** I340 `analysis.md` §§2–3 and `i340-parent-path-transfer.md`, both in full.
- **Round 1:** `review.md` in full and the manifest. The brief was read in full.
- Unchanged passages outside the context ranges were not reread. The exact diff shows they are byte-identical to the round-1-reviewed text, and no substantive concern called for expanding to a full proof reread.

## 7. What was not done

- I did not audit H's truth; it is stipulated.
- I made no novelty, priority, acceptance or count assessment.
- I did not compile Lean.
- I did not rerun the round-1 independent controls.
- I did not use subagents.
- I did not edit, stage or commit anything outside this directory, and I did not upload or submit anything.
- Temporary copies are in `/tmp/kmr2-patch`, `/tmp/kmr2-uWUL`, `/tmp/kmr2-build-wztl` and `/tmp/kmr2-render-cGhz`.
