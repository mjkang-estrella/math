# T337E contribution review, round 1

Reviewer role: independent contribution gate (first independent round). Date 2026-10-18.
Owned directory: `frontier/campaigns/2026-10-14/t337e-contribution-r1/` only.
No acceptance, count, ledger, staging, commit, upload or publication action was taken. No nested agent was used. The parallel proof reviewer's draft was not read.

## Verdict

**CONTRIBUTION: TECHNICAL** for the full, unchanged T337E scope.

Mathematical correctness of the author proof was *assumed* for this gate only, as instructed. This verdict is not a proof PASS. It is not DUPLICATE: no exact prior statement of the full theorem was found in the bounded search. It is not INELIGIBLE: no earlier campaign developed this equality target. It is not BLOCKED: the reading gaps (chiefly the unread Lytchak proof body) concern classical inputs whose status does not change the classification.

Reason in one paragraph. Every analytic piece of equality information used by T337E is produced by stipulated source operations evaluated at equality. The offset-sphere identity it records is the same identity as the smooth companion's `eq:offset-sphere` and Schulze's `2x_3=|x|^2`. The final identification is the classical "1-Lipschitz map of boundary degree one plus equal masses gives an isometry" paradigm (Burago–Ivanov; Basso–Creutz–Soultanis Theorem 1.2), or Stadler's folklore Proposition A.1. The proposed residual is a scalar-normal contraction in the tangent cone plus a local-degree certificate. In Euclidean or smooth Cartan–Hadamard ambient spaces, it is a half-page orthogonal-decomposition construction (§3 below). In singular CAT(0) spaces it is that construction transcribed with standard comparison geometry: the logarithm contraction, Lytchak differentiation, and the flat-strip/parallel-set splitting. Its degree computation is a standard blowup made immediate by exact radial preservation. This is a robust equality transfer, not a substantial new bridge. The n>2 branch is, by the author's own assessment, a threshold reuse of source04–07.

## 1. Inputs authenticated before trust

* External anchor of the author's `manifest.json`: `701a9549aa13d547f101ef9dd4ff3c890274384fef4020f6d20bc8b4c7faaa20` (recomputed, matches). `proof.md` `0b8a1c15…5a7d`, `original-scope.txt` `f16d3a1a…70b9` match the dispatch.
* An independent Python walk (not the author verifier) reproduced exactly 88 payload files and 20 directories, no links, hardlinks or non-regular files, and every manifest hash.
* Canonical `sources/preprints-tree.json` in the repository: SHA256 `eeecc1da…dc5e09b`, 13223 entries, `truncated: false`. The packet's private copy is byte-identical.
* All 43 `canonical-bindings.json` records: the local file's Git blob SHA1 equals both the recorded blob and the canonical tree's blob for that path, and the SHA256 matches. Selection completeness: for the 337 filling, 337 smooth and 081 prefixes, every canonical blob except `paper.pdf` is bound.
* pdftotext 26.01.0 `-layout` replays of `schulze2020`, `stadler2212`, `basso2209` are byte-identical to the packet text files.
* Author scripts (`verify.py`, `controls.py`, `diagnostic.py`) were read before running. They were run only on a fully authenticated disposable copy (`/var/tmp/t337e-contrib-r1-YzJ51Z/pkt`, whole-tree equality with canonical checked first). Results are in `author-controls-result.json`. The positive anchor passed (88/20). A 64-zero anchor and a 63-character anchor were both rejected with `external anchor mismatch`. The author's 13 copied mutations were all rejected. My own reason-checked replay covers 18 cases (positive, 15 mutations and 2 re-anchored counterfeits); each was rejected for the exact expected reason. Integrity only; no checksum is mathematical or novelty evidence.

## 2. Scope, chronology and eligibility

* **Scope.** The scope is unchanged and complete: every n≥2, every proper CAT(0) space, every nonzero compactly supported integral n-cycle with arbitrary integer multiplicities, and a filling infimum over all finite-mass integral fillings. It asserts equality iff the cycle is the multiplicity-one oriented boundary of an isometric closed Euclidean (n+1)-ball. No stability claim is made. This review assesses exactly that statement. No lower-dimensional, smooth-ambient or quantitative rescue is considered.
* **Chronology.** The freeze stamp is `2026-10-18T10:18:53.247434Z`. The file mtime of `original-scope.txt` is 03:18:53.2476 −0700, which agrees. The Stadler, Schulze and smooth-companion receipts and `337-working-interface.md` predate the freeze (03:09–03:14 −0700). The Basso–Creutz–Soultanis PDF and receipt postdate it (03:26:50 −0700). The scope's named source-essential operation (scalar-normal collapse, local degree, interior-ball certificate, classical density-one rigidity) is the one carried out. The freeze is after exploration, as the scope itself says, so it gives no pre-exploration protection. Mtimes are author-controlled and are weak evidence only.
* **Family history.** I read the full I286 report and parent disposition. I286 is a dimension-only positive-deficit stability target for smooth Cartan–Hadamard regions, remains unresolved, and is neither solved nor replaced here. In I91, the relevant §6 (lines 290–312) and the opening were read. I91 uses source337 `lem:opposite-average` only as a non-applicable comparator for a finite Fano configuration. The r34 history screen and the r51 reading-limits mention 337 only as an exclusion pointer to I286. An `rg` search over `frontier/` for the 337 manuscript titles and "Cartan–Hadamard" found no other campaign or iteration that developed CAT(0) filling equality. Opening081 repeated r27 and was not nominated; it is unrelated to T337E. **Eligible.**

## 3. Operation-by-operation comparison

The Euclidean template is the operational baseline used below. It comes from an elementary calculation, not from a literature claim. Let X=R^N and let A be an equality 2-cycle normalized to M(A)=4π. Take a regular point x with chart plane T, and write r=|y−x|. The scalar identity (6), |D_x d_y|²=1−r²/4, says |P_T(y−x)|²=r²−r⁴/4 and |P_{T⊥}(y−x)|=r²/2. The map

  f(y) = (P_T(y−x), |P_{T⊥}(y−x)|) ∈ R²×R

is 1-Lipschitz, because orthogonal projections and the norm are 1-Lipschitz. It maps spt A into the unit sphere centred at (0,0,1) and satisfies |f(y)|=|y−x|. The same construction works in a smooth Cartan–Hadamard manifold with exp_x⁻¹ in place of y−x, since exp_x⁻¹ is 1-Lipschitz there. T337E §§5–7 is this construction, followed by a degree count and volume rigidity, with T_xM replaced by the CAT(0) tangent cone.

| T337E operation | Antecedent actually read | Classification |
|---|---|---|
| Sharp inequality, compact minimizers, Euclidean chart mass, integer lower density (§1) | source337 `thm:main`, 02 `thm:current-background`, `prop:chart-mass`, `lem:euclidean-density` (statements read; 02 bodies not fully re-read here) | Paid, stipulated |
| Equality ⇒ extremizer inequality (1) | source337 02 `eq:extremizer`, `eq:normalization` (the source's 03 proof uses only these) | Paid; direct subadditivity |
| Radial variation (2) at equality | source337 03 `prop:radial` (full proof read) | Paid; used verbatim |
| n=2 inverse-square test, completed square, density exactly π, scalar identity (5)–(6) | source337 03 `prop:base`, `eq:base-cutoff-estimate` (it literally writes 2b−2b²=½−2(b−½)²); smooth08 lines 150–225 (the same punctured square giving t=h/2); Schulze §6 (6.5), (6.8) (unit density and H+4(∇r)^⊥/r=0 at equality) | Paid; the equality branch of an existing square |
| Offset-sphere identity |w|²+(h−1)²=1, h=r²/2 (9)–(11) | smooth08 `eq:offset-sphere` (|v+RN|=R); Schulze §6 `2x_3=|x|^2` in a fixed 3-plane | Same identity; T337E records it after collapsing the normal factor |
| Tangent-cone realization of the chart plane (§5) | Lytchak 2004 Theorem 1.6 and §7.7 (author access only; not read by me); used identically in Stadler Sublemma A.2 (read) | Classical |
| Derivative identification by the two-sided squeeze (8) | First-variation/cosine-law comparison in the cone; the author's derivation is short | Routine comparison geometry |
| Parallel-set lemma: Pythagorean distance to a flat ⇒ v∈P(E)=E×N | Parallel-set splitting (Stadler §2.6, read; Bridson–Haefliger II.2.14). For each line L⊂E through the foot point, the identity gives right comparison angles on both sides, hence flat triangles (flat-triangle lemma) and a flat strip (flat-strip theorem). The parent's Busemann proof is an equivalent few-line derivation. | Routine corollary of classical splitting |
| Scalar-normal collapse f=(w,d_N(n,n₀)) (10) | The CAT(0) analogue of (P_T, \|P_{T⊥}\|) in the template above; nearest-point projection to a closed convex set is 1-Lipschitz | The proposed residual; technical transcription |
| No cancellation: f#A=±[[Σ]] via blowup (§6) | Constancy plus continuity of pushforward under uniform Lipschitz convergence, both standard. Exact radial preservation makes f⁻¹(B_ρ(0))∩spt A=B_ρ(x)∩spt A immediate. Density one (7) is paid by the source square. | Standard degree computation |
| Interior point and volume rigidity (§7) | Stadler 2212.07100v1 Proposition A.1 and full proof (read), described by its author as folklore. Alternatively Basso–Creutz–Soultanis 2209.12545v3 Theorem 1.2 (statement and full §4 proof read): applied to the integral current space of the minimizing filling S, with f, C=B̄₁(c), f#[[∂S]]=±[[∂C]], M(∂S)=4π and M(S)=ω₃, it gives that f is an isometry directly. BCS §1.1 names this "1-Lipschitz degree-one map plus volume bound" paradigm after Burago–Ivanov and Besson–Courtois–Gallot. | Paid. The strategy "construct a contraction to the model, then apply Lipschitz-volume rigidity" is classical. |
| n>2: Λ=S_* by contradiction, constant minimizer, chord bound at W=s_n, barycentric variance, centred sphere, cone filling, Stadler (§3) | source337 05 `prop:minimizer` (strictness at lines 384–398 read), 06 chord bound and `rem:chord-sphere` (read 440–507), 07 full `lem:opposite-average` and conclusion (read). Same pattern as smooth08 for m≥3 (spectral gap, barycentre, centred sphere; read). | Technical threshold reuse; the author concedes this |
| Converse (§8) | source337 08 Euclidean sharpness and constancy (read); DLPS 2502.03389 Proposition 7.1 uses the same convex-retraction-plus-constancy step (read) | Classical |

**The strongest case for SUBSTANTIAL, and why it fails.**
(i) The full theorem appears new. Almgren covers only the Euclidean ambient, Schulze Theorem 1.3 only smooth Cartan–Hadamard ambients with n=2, and the smooth companion only bounded finite-perimeter sets in smooth Cartan–Hadamard manifolds. Druţu–Lang–Papasoglu–Stadler (Feb 2025) record that even non-sharp Lipschitz-ball versions were missing. The sharp current inequality itself exists only in the stipulated source.
(ii) Schulze's normal-alignment step needs the weak mean-curvature vector H, which a singular equality current lacks. T337E sidesteps alignment instead of reconstructing it.

However, the campaign rule classifies by operations, not by title or generality. Points (i) and (ii) concern scope and an obstacle that is avoided rather than overcome. The avoidance uses no new estimate, compactness, regularity or rigidity theorem. Discarding the normal direction is exactly what the classical Lipschitz-volume rigidity paradigm makes harmless: the map need only be 1-Lipschitz with the right boundary degree and mass. Building such a map from a scalar normal length is the Euclidean orthogonal-decomposition map above. In the singular setting it requires only the classical tangent-cone and parallel-set facts, and the parallel-set step is a direct corollary of the flat-strip theorem. The degree step is a standard tangent-cone blowup made trivial by the radial-preservation identity. Taken together, this is a careful and correct-looking assembly, and a reasonable new-to-project equality corollary. It is the kind of robust equality transfer the acceptance rules exclude ("routine transfers … do not count").

**Duplicate assessment.** In the bounded search, no source states the full singular-CAT(0) equality theorem. Duplicate sub-cases exist:
* X=R^N: Almgren 1986, equality for integral currents in all dimensions and codimensions (statement as quoted in Schulze Theorem 1.1 and source337 introduction; Almgren's body not read).
* Smooth Cartan–Hadamard X with n=2: Schulze Theorem 1.3 (κ=0), for an integral 2-cycle with arbitrary multiplicity, giving unit density and a flat 3-ball.
* Smooth Cartan–Hadamard X, codimension one, T=∂[[E]] with E bounded of finite perimeter: smooth companion `thm:equality` plus source08 top-dimensional constancy. This covers multiplicity-one boundaries; codimension-one cycles bounding integer-multiplicity top currents are not literally covered.
The uncovered remainder (singular CAT(0) for every n≥2, and higher codimension n>2 in smooth Cartan–Hadamard manifolds) is reached by the technical operations above. Hence TECHNICAL, not DUPLICATE.

## 4. Objections

Required (for any later use of T337E as technical research or in any manuscript):

* **R1. No substantial credit or count.** The contribution classification is TECHNICAL. No acceptance follows from this gate, and no narrower or quantitative substitute is to be offered.
* **R2. Antecedent table correction.** `contribution.md` must add Almgren's Euclidean equality case (all n, all codimensions, integral currents) as a covered sub-case. It must also state that Schulze Theorem 1.3 already settles the smooth Cartan–Hadamard n=2 sub-case, and that the smooth companion `thm:equality` settles multiplicity-one codimension-one boundaries in smooth Cartan–Hadamard manifolds.
* **R3. Credit for the residual's ingredients.** These must be explicit. The scalar identity and density one are the equality branch of source337 03 `prop:base`. The offset-sphere identity is that of smooth08 `eq:offset-sphere` and Schulze §6. The contraction-plus-degree-plus-mass rigidity strategy is Burago–Ivanov / Basso–Creutz–Soultanis Theorem 1.2 (and Stadler A.1). The parallel-set lemma is a corollary of the classical flat-strip and parallel-set splitting theorems. The parent supplied the Busemann proof and the radial-preservation noncancellation idea, and is credited as author assistance.
* **R4. Novelty wording.** Any wording must say "no exact prior statement found in a bounded search", not "new to the literature". The Lytchak proof body, Almgren's body, Del Nin–Perales and Bridson–Haefliger were not read in this round (see reading-limits.md).

Optional:

* **O1.** Basso–Creutz–Soultanis was acquired after the freeze. It does not alter the scope, but the chronology note should say so explicitly.
* **O2.** Using BCS Theorem 1.2 in place of Stadler A.1 would shorten §7 (no interior point or monotonicity is needed). This makes it even clearer that the final step is paid.
* **O3.** `extra337-primary-receipts.json` records the Schulze URL unversioned (`/pdf/1802.00226`). The extracted text identifies v3 (4 Feb 2020). The receipt should name the version.
* **O4.** The finite rational diagnostic is irrelevant to contribution, and the author correctly labels it as diagnostic only.

What would change this verdict: an independent proof review showing that a step assumed classical here genuinely fails. Examples are the parallel-set membership from the Pythagorean identity in a non-locally-compact tangent cone, or the cone realization of the chart plane. If such a step then required a genuinely new argument, a new round with that argument could reassess. Under the instructed correctness assumption, no such step appears.

## 5. Reading and search limits

See `reading-limits.md` and `search-log.json`. Bounded absence is not a worldwide novelty claim.

## 6. Seal

`manifest.json` lists every directory and every regular file except itself with SHA256. Its own SHA256 is reported externally and is not stored here. `python3 verify.py ROOT ANCHOR` rejects links, hardlinks, non-regular files and any inventory change. It also rechecks the retrieved DLPS PDF and text against `search-log.json` and the recorded author-packet anchor. `controls.py` runs reason-checked mutations on a disposable copy; its result is `controls-result.json`. Integrity only.
