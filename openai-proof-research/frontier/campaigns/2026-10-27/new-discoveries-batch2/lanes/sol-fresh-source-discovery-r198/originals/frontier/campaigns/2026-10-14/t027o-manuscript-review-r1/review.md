# T027O manuscript v1: independent full-manuscript review, round 1

Verdict: **PASS_FULL_MANUSCRIPT_T027O**

Required objections: **none**. Optional objections: O1–O5 below.

This review is a gate report only. It makes no acceptance decision and no
change to any count, index, release record, or frozen packet.

## 1. Object reviewed

| Item | Value |
|---|---|
| Packet | `frontier/campaigns/2026-10-14/t027o-manuscript-v1/` |
| External manifest SHA256 (dispatch anchor) | `2c9715e9a6825726d3bc630b31e7ecf214071e4878cf74d0706b1bc8c63da3dc` (recomputed, matches) |
| Packet `verify.py` SHA256 | `b6610e41…32b4` (matches dispatch) |
| `output/article.pdf` SHA256 | `84d08097231e89cbcb5a0341cb044676568b2f0f03ee70e2e63b716bcf278cb9` |
| Title / author | *One integral mapping-class orbit in every rank* / Myeongjin Kang, no affiliation |
| Pages | 16, A4 |

Upstream anchors recomputed and matching the dispatch: proof-r1 `880af01c…`,
contribution-r1 `e8bbf2c9…`, formal-review-r1 `2d71cfd5…`, formal-v1
`b35948fd…`, fresh-arithmetic-discovery-r36 manifest `2127e23f…`,
`candidate027o.md` `e5812790…`, scope record `0f53abf3…`.

Packet verifier: `verify.py --anchor <dispatch anchor>` →
`PASS_MANUSCRIPT_IDENTITY_ONLY` (133 payloads, 134 files, 20 directories,
13 source blobs, 15 primary files, 16 pages); zero anchor → rc 1,
`INTEGRITY_REJECT: external manifest anchor mismatch`. Packet
`integrity-controls.py --scratch /var/tmp` → rc 0,
`PASS_COPIED_IDENTITY_CONTROLS`, all 14 cases passing on exit code and
expected reason (positive, wrong-anchor, payload-byte, missing-file,
extra-file, extra-directory, root-link, ancestor-link, payload-link,
hardlink, fifo, nested-manifest, manifest-hardlink, self-reseal). I read
`verify.py`, `integrity-controls.py` and `public/build.py` in full before
running them. `git status` reports the packet and all frozen inputs clean.

## 2. Theorem and scope verdict

Theorem 1.1 as printed: for every g ≥ 2 and r ≥ 2 there is a number field
L, a homomorphism ρ₀: π₁(Σ_g) → SL_r(O_L), and its orbit under the
orientation-preserving mapping class group is Zariski dense in the entire
complex SL_r character variety X_{g,r}.

Scope verdict: **full original scope**. All g ≥ 2 and r ≥ 2; one actual
integral representation (6.1); one orbit; density in all of X_{g,r}, not a
component, fiber, or relative variety. Rank 2 is imported from Coccia–Litt
with explicit credit (golden-ratio unit meets their Prop. 5.0.1 unit
hypothesis; Prop. 3.1.10 gives single-orbit density; Γ_{g,0} there is the
pure orientation-preserving mapping class group, which for closed surfaces
is Mod(Σ_g)). For r ≥ 3, §§2–7 give the construction and proof. The field
dependence is stated as depending on r only for r ≥ 3; this is valid
because L is the splitting field of the Pisot-unit polynomial adjoined η.

The single upstream input is the determinant-one assertion inside the proof
of `prop:surface-irreducibility` in the pinned source (lines 110–264 of
`surfaces.tex`): the SL_n fiber S_C(c) at c = 1 is irreducible of dimension
(2g−1)(n²−1), proved before the passage to G_m^{2g}. I checked that the
manuscript (§1.3) quotes exactly this intermediate assertion and does not
use the stronger GL statement. Per AGENTS.md the pinned source is
stipulated true.

## 3. Proof reconstruction

I reread every section against the frozen candidate `candidate027o.md`
and rederived each step independently. The manuscript tracks the candidate
step for step; every difference is an E1–E6 clarification. I found no
substantive mathematical change, consistent with
`checkpoint.json: substantive_mathematical_changes = false`.

- **§2 arithmetic.** X^r − c₀X^{r−1} − 1 with large c₀ is an irreducible
  Pisot-unit polynomial; its roots are multiplicatively independent modulo
  the forced relation; μ_i = ηα_i has product 1. Density of B(m) in T and
  of SL_r(Z) in SL_r(C); integrality of C = QC_μQ⁻¹ over O_L. Correct.
- **§3 curves (E4).** Rose order, chord pairs for bd₀ and abcd₀, extra
  handles; b ↦ ba^m and d₀ ↦ d₀c^n are twist powers about a and c on
  cut annuli; a ↦ ab is the twist about b; u₀ = b a^k d₀ c^l and
  u₁ = a b a^{k−1} c d₀ c^{l−1}. The obsolete a^k b c^l d word is not used.
  Correct.
- **§4 linear algebra (E1, E5).** Lemma 4.1 sets the four stated entries to
  1 and all other off-diagonal entries to 0; the two projected entries
  differ by exactly one and det = 1. (P2) includes the discriminant.
  Lemma 4.2 (triangle coboundary/principal-minor rigidity) proved
  directly, Loewy and Mantelos credited. Proposition 4.3 symmetric/skew
  degeneration and the augmented map sl_r ⊕ 𝔥 ⊕ 𝔥 → sl_r ⊕ sl_r, injective
  iff the residual system is injective and 𝔥 ∩ 𝔥_C = 0. Correct.
- **§5 tangents (E6).** Identity (5.3) and Vandermonde in k; positive
  powers of C are Zariski dense in T_C (Laurent-polynomial recurrence
  argument is valid); (5.4) with (P1) gives W = 0; Lemma 4.2 gives h₀;
  gauge (5.5) and relation (5.6); second band (5.7) and determinant
  trace argument tr(N⁻¹[R,N]) = 0; reduction to (4.2); Prop. 4.3 forces
  S = 0. Irreducibility (B-invariant subspaces are coordinate sums, C has
  no zero entry), submersion via common centralizer 𝔥 ∩ 𝔥_C = 0, dimension
  3(r²−1) and quotient dimension 2(r²−1). Prop. 5.2: extra handles add
  tr(U_kl δA_i), −tr(U_kl δB_i) with no core subtraction; U_kl span M_r
  by Vandermonde in A and row interpolation through Q with all Q_ij ≠ 0;
  quotient dimension (2g−2)(r²−1). Finite list F. Correct.
- **§6 selection (E2).** Order: F at one complex point, then integral
  (B,Q), then complex A. Lemma 6.1 rank 2gq − q with q = r² − 1; the
  minor is a Laurent polynomial in A regular in (B,Q); dominance of each
  band spectral map A ↦ char(A^k B C^l_μ) tested at Q = I. Lemma 6.2:
  failure of cyclic density in a diagonal torus ⇔ χ(t) = 1 for a
  nontrivial χ ∈ Z^r/Z(1,…,1); countably many proper closed sets plus the
  explicit discriminant locus; Baire on a closed ball in the A-torus.
  (6.2) puts every [ρ_A] in the closure of the orbit of the integral seed
  via a ↦ ab and density of ⟨B⟩ in T. Correct.
- **§7 closure (E3).** Lemma 7.1 via the finite-étale eigenvalue-ordering
  cover, component dominance, and nonresonance density; Lemma 7.2 HNN
  gluing torus, positive power τ^{n_γ} preserving Z₀, and density of
  powers of a cyclically dense element in its connected torus; holomorphic
  Hamiltonian convention with Ω = Re ω, Re h ↔ X_h, Im h ↔ −iX_h, Goldman
  Lemma 1.11 and Theorems 4.3/4.5/4.7 with (4.6); Lemma 7.3 coherent
  radical ideal sheaf and holomorphic ODE uniqueness through singular
  points of Z₀; final inverse-function argument with d = (2g−2)(r²−1)
  flows and irreducibility of X_{g,r}. Correct.

## 4. Dispositions

### Proof findings E1–E6 (t027o-proof-r1)

| ID | Location | Disposition |
|---|---|---|
| E1 | Lemma 4.1, §4 | Implemented: all other off-diagonals zero, projections (1,1) and (d₁+d₂, d₁+d₂+1), det 1. |
| E2 | Lemma 6.2 | Implemented: discriminant of each band spectral map avoided explicitly. |
| E3 | §1.3, §7 before Lemma 7.3, Lemma 7.3 | Implemented: ambient smooth irreducible D/G locus, Re/Im Hamiltonian correspondence, Goldman citations, coherent ideal and ODE uniqueness. |
| E4 | Lemma 3.1 and following text | Implemented: actual twist powers, cut-annulus description, relator identities. |
| E5 | Prop. 4.3, (4.3) | Implemented: explicit augmented map and injectivity criterion. |
| E6 | Prop. 5.2, (5.9) | Implemented: no subtraction asserted. |

### Contribution credits C1–C4 (t027o-contribution-r1 required credits 1–4; author crosswalk R1–R4)

| ID | Location | Disposition |
|---|---|---|
| C1 | §1.1–1.2, refs [4],[5] | Implemented. GT PNAS Theorem I (rank 2) and §2.4 remark 2 (Larsen–Pink SL_d "should be able to") checked in the retained PNAS body; the SL_d extension is labeled unproved. PNAS title *Closure of orbits…* and preprint title *Orbit closure…* both correct. |
| C2 | Abstract, §1.2, A.2 | Implemented. Theorem positioned as a special case of the anticipated higher-rank picture; claim limited to new to this project with bounded search and no priority clearance. |
| C3 | §1.1, refs [6],[12] | Implemented. Litt Thm 5.4.13 and proof sketch checked; Shimura/unitary-conjugate route credited; GT exceptional-locus caveat attached to Previte–Xia Thm 1.4; neither used as a proof input. |
| C4 | §1.2, refs [1],[9] | Implemented. BKMS Prop. 1.2 checked: GL_n(C) characters fixed by Mod(S,*), infinite image, via Thm 5.1. The manuscript states it precisely and keeps the MathOverflow thread as a discussion pointer only. |

Additional credits checked: Pickrell–Xia Prop. 2.1.24 and Lemma 2.1.34
(compact K, generic) cited next to §5 and in §1.2, with the compact /
generic / centralizer-power distinction. The pants-torus dimension
comparison (3g−3)(r−1) < (g−1)(r²−1) = ½ dim X_{g,r} is explicit in §1.2
and is stated for r ≥ 3, which is exactly its range of validity: dividing
by (g−1)(r−1) > 0 it is 3 < r + 1, with equality at r = 2. Source027's
fixed-spectrum-fiber saturation/Baire/submersion operation is credited in
§1.2 and §7.

### Scoped formal findings F1–F4 (t027o-formal-review-r1)

| ID | Location | Disposition |
|---|---|---|
| F1 | A.1 | Implemented: the rational counterexample shows genericity cannot simply be deleted; no claim that every triangle condition is necessary in larger index sets. |
| F2 | A.1, Lemma 4.2 | Implemented: lower-order identities stated before identifying pair/cycle expressions with minor derivatives; reviewer additions in `T027OReview.lean` distinguished from the author package. |
| F3 | Crosswalk, proof-scope | Implemented as a records matter: no formal rebuild by the manuscript author; receipt flags described as constants. |
| F4 | Crosswalk, proof-scope | Implemented: no strengthening attributed to the frozen author controls; manuscript controls check exit status and reason (confirmed by running them). |

A.1 states clearly that the Lean artifact is not a formal proof of
Theorem 1.1 and covers only the scalar identities of Lemma 4.2.

## 5. Primary sources

Thirteen pinned source blobs re-hashed against `sources/preprints-tree.json`
(complete, not truncated). Retained primary bodies read at the cited
passages: Coccia–Litt (Γ_{g,n} definition, Prop. 3.1.10, Prop. 5.0.1,
Thm 5.0.2), GT PNAS and preprint, Litt 2409.02234v1 §5.4.10–5.4.14, BKMS
NYJM 24 (2018) Prop. 1.2/Thm 5.1, Goldman Invent. Math. 85 (Lemma 1.11,
Thms 4.3/4.5/4.7, (4.6), §3.16), Mantelos Lemma 6.2, Pickrell–Xia CMH 77
Prop. 2.1.24 and Lemma 2.1.34. All descriptions in the manuscript match.
Primary copies are byte-identical across contribution-r1, r36 and the
manuscript packet; all 12 provenance copy receipts match live files.
Unread or unretained items are listed in `reading-limits.md`.

## 6. Reproducibility and page inspection

Fresh build of a copied `public/` with Tectonic 0.17.0 (`--only-cached
--untrusted`, `SOURCE_DATE_EPOCH=1792281600`, `TZ=UTC`, binary SHA256
`a98aa59a…46da`) → rc 0, PDF byte-identical (`84d08097…8cb9`). Log has no
missing characters, undefined references or undefined citations; it has
one `Underfull \hbox (badness 10000)` (O1). Fonts all embedded; metadata
title, author and epoch-derived creation date correct.

All 16 pages rendered with `pdftoppm -r 110 -png` and inspected visually
by this reviewer one at a time. Renders are byte-identical to the author's
`inspection/` PNGs. No clipping, overlap, missing glyphs, broken equation
or cross-reference labels, or page-number problems. The only visible
blemish is the stretched interword spacing in bibliography entry [8] on
page 16 (O1). Per-page record: `page-inspection.json`; build record:
`reproducibility.json`.

## 7. Licensing, authorship and private bodies

`public/LICENSES.md`: prose CC BY 4.0, code MIT, author Myeongjin Kang,
no affiliation. Title page and PDF metadata agree. The acknowledgment
discloses AI assistance and places responsibility with the named author.
`.gitignore` excludes `/private/`; `git check-ignore` confirms the private
primary and preprint files are ignored; the public source bundle contains
no third-party bodies. This review directory retains no third-party bodies.

## 8. Objections

Required: **none**.

Optional (none affects correctness, scope or credit):

- **O1 (layout/tooling).** `Underfull \hbox (badness 10000)` at
  `references.tex` lines 45–49, the Mantelos entry [8]; visible as
  stretched spacing on page 16. `build.py`'s warning filter ignores
  Underfull messages, so its `layout_or_reference_warnings` is `[]`, and
  the author page record does not mention it. Fix by setting that entry
  ragged-right as was done for [10], and by widening the filter.
- **O2 (disclosure).** I did not read MathOverflow 332994 myself; no
  local copy exists. Kapovich and Lawton content is corroborated by the
  author and contribution-r1 reading records. The asker attribution
  "C. Frohman" and the "2019" date are not verified by this review. The
  item is a pointer only; retaining a private snapshot would close this.
- **O3 (disclosure).** Previte–Xia TAMS 354 (2002) 2475–2494 is not
  retained. Metadata agrees across three independent bibliographies (Litt
  PX02b, GT PNAS ref. 4, GT preprint ref. 30), and GT PNAS cites the same
  Theorem 1.4. Loewy (LAA 78) is also unread; Lemma 4.2 is proved in full
  in the manuscript, so neither is a proof input.
- **O4 (records).** The frozen `t027o-formal-v1/README.md` still calls
  genericity "mathematically necessary". The manuscript's A.1 wording is
  correct (F1). A release record could note the superseding wording.
- **O5 (exposition).** A.1 refers to `t027o-formal-v1/README.md` for the
  Lean/mathlib pins and trusted build boundary. Stating the pins directly
  in A.1 would make the PDF self-contained on this point.

## 9. Sealing

Directory inventory is sealed by `manifest.json`; `verify.py` requires the
external SHA256 of `manifest.json` as its single argument and never
reseals. `controls.py` runs positive, wrong-anchor, short-anchor and
mutation cases on fresh copies under `/var/tmp` and checks both exit code
and failure reason.
