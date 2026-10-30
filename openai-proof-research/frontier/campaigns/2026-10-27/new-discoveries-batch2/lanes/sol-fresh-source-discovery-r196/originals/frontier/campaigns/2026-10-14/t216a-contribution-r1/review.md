# T216A independent contribution/eligibility review r1

Reviewer role: independent CONTRIBUTION/ELIGIBILITY gate for the frozen T216A author packet `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r49/`. Written 2026-10-18 (UTC). This gate is not author assistance and does not adopt or count anything. The parallel proof review and its draft were not read. Only this directory was written.

Pinned source truths at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. For this gate the unchanged full proof is assumed correct, as instructed. Nothing here is a proof verdict. Count 13/20 and target 20 were given no weight.

## Verdict

**CONTRIBUTION_TECHNICAL** for the full, unchanged T216A scope (exact $m(h)/[h^{1/15}(\log 1/h)^{1/15}]\to C_m$ along all real $h\downarrow 0$, with the $(15/16)C_m$ pressure limit).

- Not SUBSTANTIAL: every operation in the residual (the ultraviolet Dirichlet/whole-plane boundary-pressure comparison, its phase/small-ball/collar steps and the source-specific assembly) has a direct operation-level antecedent in papers I actually read, with one caveat: the lattice sandwich (C5) also reuses the Ginibre correlation comparison, which r48 already used and which I did not read myself (MMP Proposition 1 was read). The one operation without a verbatim antecedent, the Gaussian harmonic small-ball replacing the Ising RSW/FKG shielding event, works with a very large margin, $\exp(-C\log^2 t)$ against the scale $\exp(t^{16/15})$, so it is a robust substitution, not a new estimate at a sharp threshold.
- Not DUPLICATE: no located source, companion or literature item states the XY magnetic amplitude. The full theorem depends on the pinned 2026 family216 center amplitude $A_{XY}$, so no earlier paper can contain it. No family216 companion contains a positive-field pressure or magnetization asymptotic (all 68 canonical-matched family216 `.tex/.md` blobs were searched; see Limits).
- Not INELIGIBLE: the target is the disclosed continuation of r48, frozen after exploration, unchanged, with parent co-authorship disclosed. Chronology observations are recorded below; they lower the evidential weight of the freeze but do not exclude the target.
- Not BLOCKED: Gielerak 1986 remains unread in body (retrieval failed again, see Limits). Its content can only shrink the residual further, so it cannot move this verdict toward SUBSTANTIAL. It also cannot make the full theorem DUPLICATE, because the lattice XY amplitude requires source216. The TECHNICAL verdict therefore rests entirely on read antecedents, and Gielerak is not decisive for it. It remains decisive for whether the continuum component is itself an already-published result.

## Operation-level correspondence

Notation follows the author packet: $D=(-1,1)^2$, $\beta=1/2$ in log-one normalization, $\mu_D$ the ultraviolet-only Dirichlet chaos, $\mu_*$ the whole-plane chaos with independent uniform phase, $F_D(t)=\log E e^{t\,\mathrm{Re}\,\mu_D(D)}$, $F_*(t)$ likewise, $p=16/15$.

### C0. Scaling turns the continuum lemma into a thermodynamic boundary-independence statement

By exact ultraviolet scaling, $t\,\mu(D)$ has the law of $\mu(L D)$ with $L=t^{8/15}$. So $F_\bullet(t)/(4t^{16/15})$ is the pressure per unit area of a unit-fugacity two-dimensional Coulomb gas (sine-Gordon) in the box $LD$, with Dirichlet or whole-plane ("free") boundary conditions. The author's "continuum boundary-pressure identity" is exactly the classical question of whether the infinite-volume pressure depends on boundary conditions, at $\alpha=1/8$ in Fröhlich's notation. This is the same reduction CGNII uses (Proposition 2.6 scaling plus Theorem 2.7 free energy, text lines 247–300).

### C1. Whole-plane coefficient $c_*$: paid

- Fröhlich 1976 §4, Theorems 4.5 and 4.7 (text lines 1111–1250): for $\alpha=\beta e^2/4\pi<1$, the neutral massless Coulomb gas in rectangles has pressure $p(\alpha,z)=F(\alpha)z^{2/(2-\alpha)}$ with $0<F<\infty$. In the T216A normalization the pair weight is $|x-y|^{\pm 1/4}$, so $2\alpha=1/4$, $\alpha=1/8$ and $2/(2-\alpha)=16/15$. The uniform-phase expansion $E e^{t\mathrm{Re}\,\mu_*}=\sum_k (t/2)^{2k}(k!)^{-2}E|\mu_*|^{2k}$ (the identity checked in the author's `diagnostic.py`) is Fröhlich's grand-canonical $Z(V_0,z\chi_\Lambda)$ with $z=t/2$. So $c_*$ is Fröhlich's $F(1/8)$ up to the fugacity convention.
- LSZ17 Corollary 1.3 and ABJJ Theorem 1.6 with Appendix B (lines 198–210, 2513–2622) give the corrected moment and tail asymptotics. The author's use of the corrected exponent 16 is correct bookkeeping, not a contribution.

### C2. Reverse inequality $F_*\le F_D$: paid

Averaging the independent harmonic part multiplies each neutral Dirichlet charge kernel by $\exp(-\tfrac{\beta^2}{2}\mathrm{Var}\sum q_j h(x_j))\le 1$, and nonneutral Dirichlet kernels are nonnegative. This is Fröhlich Lemma 2.1 and the proof of Lemma 4.1, equations (2.8)–(2.10) and (4.5)–(4.6) (lines 245–262, 1025–1060): termwise comparison of neutral partition functions when the covariance difference is positive on neutral charges. The same Jensen-on-the-smooth-part step appears in ABJJ's proof of Lemma 2.5, equation (2.10) (lines 396–436). The author correctly avoids Fröhlich Theorem 2.4 (Guerra–Rosen–Simon conditioning), which is stated for full-variance Wick ordering.

### C3. Sharp upper inequality $\limsup F_D/t^p\le\lim F_*/t^p$: routine adaptation

- Template: CGNII Lemmas 2.12, 2.14 and 2.16 (lines 438–631). Restrict to a favorable event whose probability cost is negligible on the free-energy scale (there, an RSW plus-circuit with $\liminf L^{-2}\log H=0$). Then compare a fixed interior core to the target ensemble by FKG, and remove the annulus by a separate $\eta(\epsilon)\to0$ estimate.
- T216A replaces the RSW circuit with the event that the harmonic part of the Markov decomposition is within $t^{-2}$ of a constant on the core. The cost is $\exp(-C\log^2 t)$, shown by Šidák 1967 Corollary 1 (product of marginal rectangle probabilities, text lines 171–187) and the geometric decay of harmonic Fourier-coefficient standard deviations on an inner circle. It replaces FKG with Hölder plus the sharp moment bound (JSW Theorem 1.3, lines 245–260; ABJJ Lemma 2.5, lines 379–466) to make the residual phase error $O((t\epsilon)^{p})=o(1)$.
- ABJJ Lemma 2.7 (lines 476–636) already performs the same Dirichlet-to-whole-plane harmonic-part comparison for imaginary chaos tails, using the same Markov decomposition and moment positivity. Its Lemma 2.8 has the additive error the author correctly notes. T216A changes the comparison from an additive tail estimate to a change of measure on a small-ball event. That is a known way around additive errors (it is CGNII's structure), and the cost margin is enormous: $\log^2 t$ against $t^{16/15}$. Fröhlich (2.12)/(2.27) gives the opposite inequality only with a fugacity loss (factor $2$ or $e^K$), so the sharp upper direction is not verbatim in Fröhlich. But closing it needs only the CGNII device with a Gaussian event, not a new estimate.

### C4. Whitney collar $\|\mu_D(C_\delta)\|_q\le Cq^{1/16}\delta^{7/8}$: routine

This is ABJJ Lemma 2.5 rectangle scaling and Markov phase comparison, summed by Minkowski over a Whitney cover. It is the continuum analogue of CGNII Lemmas 2.11 and 2.16, lines 360–437 and 576–623 (annulus split into squares, each bounded by a single-box free energy). The same Whitney summation appears verbatim in r48's technical transfer, equation (6), for the lattice block. The conversion $\|Y\|_q\le Kq^{a}\Rightarrow\log Ee^{tY}\le C+C(tK)^{1/(1-a)}$ is elementary.

### C5. Lattice pressure-increment sandwich (lattice-interface §4): classical

- Lower bound: Ginibre local-field monotonicity, integrated in $h$. Upper bound: MMP 1978 Proposition 1 aligned-boundary domination (statement and proof start read, lines 71–105), integrated in $h$.
- r48 already used both halves for $m(h)$: its (9) via MMP and its (12)–(13) via the Ginibre local-field tilt. Integrating these magnetization comparisons from $0$ to $h_0$ is one line.
- The r48 amplitude interface called a "uniform field-on/off boundary comparison" the missing operation. T216A shows it follows by integrating comparisons r48 already had. That reclassifies the r48 gap as an overlooked routine step. It is not evidence of a hard new estimate.

### C6. Fixed-tilt lattice block Laplace limits (1) and (2): technical, already credited

- (2) uses source S `thm:main` and `fields:law` (exponential moments, lines 456–503) plus the r48 Whitney collar, with the $\kappa$ normalization bookkeeping. The source introduction (lines 152–156) says explicitly that a free-boundary transfer "would require additional amplitude and boundary-to-bulk information"; T216A supplies it through the next item.
- (1) uses the fixed-$k$ multi-arc extension of L's pinned-sector lemma and thermodynamic bracket, which the brief credits as technical, plus the source collision and Lee–Yang operations.
- The fixed-tilt to moving-tilt uniform-integrability transfer is the JSW §4.5 operation (lines 3141–3216).

### C7. Inversion and convex secants: technical, as the author concedes

I rechecked the inversion arithmetic. It gives $h\,n^2a_n\to t$ and $C_p=c_*(\kappa A_{XY})^{16/15}(8/15)^{1/15}$ consistently.

### C8. The Ising architecture is the same

CGN12a/CGNII supply, for Ising, the continuum block Laplace transform, the scaling covariance $m_\lambda=\lambda^{15/8}m$ and boundary-independent continuum pressure $b\,t^{16/15}$. CGN12b supplies the $h^{1/15}$ order. With the classical increment sandwich (FKG/GHS versions of C5), the Ising amplitude would follow in a few lines. The reviewer derived this sketch; it is not a literature claim. A bounded search did not locate a publication stating the exact Ising amplitude, and that absence is not used as evidence either way. T216A follows this architecture with XY substitutions:
- the source's logarithmic amplitude $a_n$, which is carried purely by inversion bookkeeping;
- Gaussian Markov and small-ball arguments in place of FKG/RSW;
- the ultraviolet $\kappa$ normalization.

## Required objections

These are the decisive findings that set the verdict at TECHNICAL.

1. **R1 (residual continuum operation is a robust transfer).** C1–C4. Each step of `continuum-boundary-pressure.md` maps to a read antecedent operation:
   - Fröhlich Theorem 4.7 for the coefficient;
   - Fröhlich Lemma 2.1/4.1 for the reverse inequality;
   - the CGNII 2.12/2.14/2.16 favorable-event and collar template for the upper inequality and boundary removal;
   - the ABJJ Lemma 2.7 Markov/harmonic comparison and Lemma 2.5/JSW Theorem 1.3 moments;
   - Šidák Corollary 1 for the Gaussian event.

   The only replaced ingredient (RSW event to Gaussian small ball) has a cost margin of $\log^2 t$ against $t^{16/15}$. No sharp or threshold-sensitive estimate is new.
2. **R2 (the lattice sandwich is classical integration).** C5. It integrates the Ginibre and MMP comparisons r48 already applied to $m(h)$. Its novelty claim ("avoids O(1/n) surface energy") is a feature of comparing increments, which is standard for correlation-inequality sandwiches.
3. **R3 (source-specific assembly adds bookkeeping, not mechanism).** C6–C8. The logarithmic correction, $\kappa$ and $A_{XY}$ enter only through stipulated source theorems and scale inversion. The mechanism is the CGN Ising pressure-to-magnetization architecture.
4. **R4 (striking conclusion does not raise the classification).** The exact amplitude is a new-to-project and, as far as located, new-to-literature statement. That follows from the source being new, not from a new operation in T216A. Per the brief, the striking conclusion and the source-critical amplitude confer no substantiality.

## Optional objections and observations

These do not change the verdict.

1. **O1 (Gielerak 1986, decisive for the continuum component, not for the verdict).** I read the AIP abstract and full reference list on 2026-10-18. The abstract says the paper reduces uniqueness of translation-invariant regular tempered Gibbs states, for 2D trigonometric interactions, to boundary-condition independence of the infinite-volume free energy, via Ginibre-type inequalities, and proves that independence. It extends Albeverio–Høegh-Krohn 1979. Its references include Fröhlich 1976, Guerra–Rosen–Simon, Fisher 1965 Lemma III, Griffiths 1964 Appendix A, MMP 1978 and Ginibre 1970. These references are consistent with a van Hove-type boundary-independence argument, but **no mass, normal-ordering, coupling-range or ensemble restriction is inferred from them**. If its theorem covers the massless ultraviolet-normalized case at $\alpha=1/8$, with Dirichlet versus free/whole-plane boundary conditions, the continuum component is already paid outright (component duplicate). If it does not, R1 still stands. Body unread.
2. **O2 (component framing).** "Rigorously normalized continuum boundary pressure" is the classical boundary-condition independence of the sine-Gordon/Coulomb-gas pressure, by C0. The author packet credits Fröhlich and CGNII but does not state this equivalence plainly. A manuscript should do so.
3. **O3 (chronology).** r48 was committed at 07:17:01Z. The r49 `working-interface.md`, containing the full reduction (sandwich, normalization, conditional amplitude formula), has mtime about 07:18Z. The freeze is at 07:20:46Z, and the parent continuum lemma was committed at 07:28:09Z (`d7bfa4e1`). The target was frozen with the route already identified and about 7 minutes before the remaining lemma was written. This is consistent with the disclosure ("after exploration, before complete proof assembly"), but the freeze gives no independent evidence of difficulty.
4. **O4 (counting authority co-authored the residual).** The parent supplied the Šidák small-ball proof and the continuum assembly, which is the claimed residual. This is disclosed and credited. The parent should not rely on its own assessment of that component when adopting any classification.
5. **O5 (Barashkov–Oikarinen–Wong, arXiv 2408.16574, abstract only).** This proves small-deviation bounds for Gaussian multiplicative chaos and a nonzero finite subsequential free-energy limit for massless sinh-Gordon on tori. It is a related contemporary use of Gaussian small-deviation estimates in free-energy limits (real chaos, torus). It is not an antecedent for the imaginary-chaos Dirichlet comparison. Read at abstract level only.
6. **O6 (author's own classification is consistent).** `contribution.md` already calls the core/favorable-event/collar structure "a close strategic adaptation, not a novel general template" and declines a substantiality claim from search absence. I found nothing that overturns that self-assessment upward.

## Reading actually done by this reviewer

Line numbers refer to the author packet's `pdftotext -layout` outputs, which I re-extracted byte-identically for all ten PDFs.

| Item | Actually read | Limit |
|---|---|---|
| AGENTS.md, sources/upstream.json | full | — |
| NEW-TEN-2026-10-14.md | targeted grep, and lines 1125–1149 (r48 and T216A entries) in full | not the whole ledger |
| Author packet | original-scope, README, contribution, source-map, lattice-interface, continuum-boundary-pressure, amplitude-assembly, reading-limits, working-interface, primary-search-limit, outside-context-receipts, parent-provenance, verify.py, seal.py, controls.py, diagnostic.py, controls-result.json: full | formal-plan.md not read |
| r48 | 216-technical-transfer.md, amplitude-interface.md, checkpoint.md: full | reading-limits/manifest identity only |
| Parent | reading-receipt, reading-addendum, author-final-verification, primary-receipt, contribution dispatch JSON | proof brief and contribution brief text not read; the parallel proof-review directory not opened |
| CONTENTS.md | family216 block, lines 5004–5093 | — |
| Source S | 01-introduction lines 60–200 (laws, `thm:main`, scope remark); 07-fields label scan and lines 456–505 (`fields:law`) | no source proof audit; other S sections not read |
| Source C | introduction lines 70–110 | — |
| Source L | conclusion.tex lines 1–60 | pinned-sector lemma not re-read; credited technical per brief |
| family216 all companions | ripgrep over all 68 canonical-matched `.tex/.md` blobs for field, pressure, free energy, equation of state, 1/15, 16/15 and susceptibility terms | search, not reading; hits inspected: C intro line 87 (Kenna–Irving finite-size susceptibility prediction), not a field asymptotic |
| CGNII arXiv 1307.3926 | lines 1–699 (abstract, Theorems 1.2–1.4, §2 including Proposition 2.2, Theorem 2.7, Remark 2.9, Lemmas 2.10–2.16 and proofs) | §§3–4 not read |
| ABJJ arXiv 2401.14942 | lines 36–265 (intro, Theorem 1.6), 286–665 (§2 including Lemmas 2.1–2.8 and proofs), 2513–2622 (Appendix B) | §§3–7 not read |
| Fröhlich 1976 | lines 180–440 (Definitions 2.1–2.5, Lemmas 2.1–2.2, Theorems 2.3–2.4), 840–925 (Theorem 3.8), 990–1289 (§4: Lemmas 4.1–4.2, Corollary 4.3, Theorems 4.4–4.7) | rest not read |
| JSW arXiv 1806.02118 | lines 240–290 (Theorems 1.3–1.4); about 3070–3230 (§4.5 proof of Theorem 1.6) | display truncated about 95 lines inside these ranges |
| LSZ arXiv 1510.01955 | title/abstract/opening lines 1–30 | Corollary 1.3 used only through ABJJ Appendix B's restatement |
| Šidák 1967 | text lines 90–190 (Theorem 1, proof, Corollary 1) | — |
| MMP 1978 | Proposition 1 statement and proof start (lines 71–105) | rest not read |
| Ginibre 1970, Newman–Wu, CGN2012 | **not read by this reviewer** | C5 relies on the standard statements, r48 usage and author/parent receipts |
| Gielerak 1986 | AIP abstract page with full reference list (fetched 2026-10-18) | **body unread** |
| arXiv 2408.16574 | abstract page only | — |

## Retrieval and search limits

- Gielerak 1986 body attempts on 2026-10-18:
  - the electronicsandbooks URL over HTTPS and HTTP: connection refused (curl exit 7);
  - the same URL through the fetch tool: a binary-content refusal before any body was processed;
  - the AIP article PDF: HTTP 403 HTML;
  - doi.org: redirected to an AIP 403 HTML page.

  No body bytes were stored. No mass, normal-ordering or other exclusion is inferred.
- Web searches (bounded): the Gielerak exact title; the exact Ising amplitude $h^{1/15}$ from the continuum free energy (two queries); the critical XY magnetization amplitude; and imaginary-chaos Dirichlet/whole-plane free-energy boundary independence. No prior XY amplitude theorem and no published exact Ising amplitude derivation was located. These absences are not novelty evidence.
- Other possibly relevant unread items: Albeverio–Høegh-Krohn 1979 (CMP 68) and Guerra–Rosen–Simon 1975 (Ann. Math. 101), the classical Dirichlet/free boundary-independence antecedents cited by Gielerak; Gielerak's companion "Trigonometric perturbations of Gaussian generalized fields"; and CGN12b in its current reading (the r48 full read is inherited, not repeated). None is needed for the TECHNICAL verdict. Each could only further pay the residual.

## Integrity checks performed (identity only; no mathematics certified)

- I confirmed all 8 externally supplied author anchors by direct SHA256: manifest, verify.py, README, original-scope, lattice-interface, continuum-boundary-pressure, amplitude-assembly and contribution.
- The author verifier code was read before running it. It ran read-only on the frozen packet with the supplied anchor: `PASS_INTEGRITY_ONLY files=84 directories=15`. An all-zero anchor and a one-hex-digit-altered anchor were both rejected. `seal.py` was not run.
- The author `controls.py` ran only on a disposable copy under `/var/tmp`. Its 14 controls behaved as recorded: positive accepted and 13 mutations rejected.
- I independently hashed the canonical `sources/preprints-tree.json`: SHA256 `eeecc1da…dc5e09b`, 13223 entries, truncated false. The packet copy is byte-identical. I recomputed the git-blob SHA1 of every actual file under `private/preprints` (35 of 35; the receipt path set equals the actual file set) and matched each against the canonical tree. I also matched all 70 r48 family216 blobs (including all 68 canonical family216 `.tex/.md` files) against the canonical tree.
- The parent continuum note hash `06ae2006…` equals the packet copy. The three parent receipts equal their copies. The five outside-context receipts match. The copied `upstream.json`, `AGENTS.md` and `CONTENTS.md` are byte-identical to the live files.
- I replayed all 10 primary `pdftotext -layout` extractions into `/var/tmp`; each is byte-identical to the stored text. The authenticity of the PDFs against their publishers was not independently checked.
- The frozen r49 directory shows no git modifications.

## Seal

This directory is sealed by `manifest.json`, covering every file except itself and every directory. Verify with `python3 -I verify.py ROOT EXTERNAL_MANIFEST_SHA256`. The external anchor, the manifest hash and the verifier hash are reported to the parent outside the packet. `controls.py` runs positive, wrong-anchor and copied-mutation checks only on a fresh copy under `/var/tmp`. Hashes certify identity only.
