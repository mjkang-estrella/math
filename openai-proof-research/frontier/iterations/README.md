# Continued discovery iterations

User direction on 2026-10-08: “Iterate & discover until you get a desired output.” The previous [outcome](../OUTCOME.md) is a historical report of the first pass, not a completion claim for the resumed objective.

## Objective and success gate

Produce a genuinely new substantial theorem, or a substantial new case of a high-importance MathDB problem, through a nonroutine argument enabled by the accepted OpenAI corpus. Preserve the pinned premises and exact source contracts. A technically correct corollary, known reduction, unclosed conditional theorem, negative experiment, or new-to-project classification is not success.

Before accepting a candidate:

1. State its exact improvement over both accepted corpus and primary literature, with observed MathDB importance evidence.
2. Supply the new construction or estimate itself, with full hypotheses and quantifiers.
3. Seek counterexamples and independent proof review focused on the least justified steps.
4. Search primary prior art early and repeat the targeted check for the final statement.
5. Commit each validated substantive finding separately. Preserve failed arguments and corrections as research records, without inflating the finding count.

When a report returns without meeting the gate, integrate its evidence and use it to choose a concrete refinement or a fresh target. Do not automatically close the resumed research just because the current delegated batch finishes. Do not lower the novelty/significance standard to force success.

## Iterations 02–03 — running

| Lane | Work | Intended report |
|---|---|---|
| Cross-field, round 1 | Returned failed sunflower/Kakeya bridges and a proved rank-one perturbation obstruction; independent audit passes with prior-art qualifications. No substantial new target case. | [Report](i02-crossfield.md) |
| Operator construction, rounds 2–4 | Explicit reflection half-spaces pass independent review and rule out every T_a=S+M_aV candidate. Recorded as R005; asymmetric Q is now under investigation. | [Finding](../findings/R005-operator-reflection-obstruction.md); [audit](../reviews/i03-operator-halfspace-r4.md) |
| Arithmetic, rounds 1–2 | Corrected B/B1 pass independent proof review and parent reproduction; recorded as R004. Literature priority and the nonroutine success gate remain open. | [Finding](../findings/R004-simultaneous-bounded-index.md); [audit](../reviews/i02-arithmetic-r2.md) |
| Arithmetic, rounds 3–4 | Returned a candidate fixed-progression PD proof and positive-lower-density primitive-root deduction. Parent source/finite checks reproduce; fresh independent analytic audit is running. Not yet accepted. | [Candidate](i03-arithmetic-progressions.md); `../reviews/i03-arithmetic-progressions-r4.md` |
| Hodge construction, round 1 | Returned an explicit quotient carrier and obstructions to specific constructions; no partner cycle or new Hodge case. Parent reproduced exact checks; independent proof audit is running. | [Report](i02-hodge-construction.md) |
| Hodge construction, round 2 | Independently audit round 1, then attempt an actual curve-family/cylinder on the explicit quotient using geometry outside the excluded constructions. First turn failed at provider level; the same child task was resumed from its retained work. | `i02-hodge-cylinder-r2.md`; `../reviews/i02-hodge-construction-r2.md` |

Each lane has a T3 delegated task, with IDs in its adjacent `*-task.json` file. Completion events return to the parent thread for integration and the next decision. No recurring schedule or external publication was created.

### Hodge round 1 integration — 2026-10-08

The parent read the completed task result and full report, reproduced `experiments/i02_hodge/check.out` exactly, and verified the eight manuscript/literature hashes in its manifest plus all 37 H8 source hashes. These checks certify source integrity and finite character calculations, not a cycle construction, novelty, or the full geometric arguments. Primary-source checks of Arapura Theorems 3.2–3.4 and Ein–Lazarsfeld Theorem 1 agree with the restrictions quoted in the report. The separate independent proof review remains pending.

The constructed object is a singular threefold quotient with a 16-dimensional level-one primitive H³ block. It is not a nonzero partner CH² class. Its identification with the repaired Mumford partner is also unproved. Restriction vanishing on boundary strata by itself must not be promoted into vanishing of every Gysin/support map; round 2 explicitly audits that distinction.

Decision: retain round 1 as a research record, with no increase to the count of accepted substantial findings. Round 2 will test actual incidence families or singular supports with additional irregularity. The cross-field and arithmetic tasks were both still working when this result was integrated; their work is not duplicated.

### Cross-field round 1 integration — 2026-10-08

The parent read the completed task result and report. Its finite output reproduces exactly: twelve rational probability checks, binary sunflower-free examples through rank four, and twenty-nine rank-two determinant evaluations. The parent verified all nine recorded upstream SHA-256/Git-blob hashes, four literature download hashes, and eleven input hashes. These checks do not establish universal proofs or novelty. The parent also read the accepted operator's exact construction theorem and Tcaciuc's scalar resolvent results, and checked the report's Gaussian-growth argument: a nonconstant order-zero scalar resolvent function cannot omit 1; the alternative of zero moments gives a proper cyclic invariant subspace. Independent review remains pending.

No candidate clears the success gate. The sunflower threshold upgrade is false for unrestricted spread families, and the avoiding-set convexity application has the wrong exceptional set. The Kakeya lift recovers only dimension four. Proposition R excludes rank-one perturbations of the accepted operator, with novelty unestablished; it is recorded as an obstruction to a research route, not a substantial advance on the celebrated target.

Decision: continue with the exact rank-two transfer problem in §7 of the report. The new task must use the actual dyadic weights, test controllability/observability and ordinary invariant subspaces, and reject mere similarity constructions. If that approach yields only an elementary or known obstruction, it must attempt a materially different construction. No accepted-finding count is increased.

### Hodge round 2 execution recovery — 2026-10-08

The original delegated run reported `Provider turn failed.` It produced literature extracts but neither assigned report. The parent read its terminal status and final activity, then resumed the same child thread with an idempotent follow-up request. Its last progress note described a cubic-cover comparison and two branched incidence-family attempts; these are unverified work in progress, not accepted findings. The original task ID remains the status handle; the follow-up run receipt is in `iteration2-hodge-cylinder-r2-resume.json`. This is an execution failure and retry, with no mathematical conclusion.

### Arithmetic round 1 integration — 2026-10-08

The parent read the terminal result and full report, reproduced the finite index checks for bases 2, −3 and 12 and the QRH geometry scan, and verified all 59 files against the manifest's pinned git-blob hashes. Read source contracts include PD Theorem `thm:main` and the complete splitting section, including `spl:field-bounds` and `spl:smooth-estimate`. The latter explicitly gives a constant independent of the field; the displayed splitting bound precedes the manuscript's specialization to a shorter q range. These observations support the key dependency but do not replace independent proof review.

The candidate gives bounded index for any fixed finite set of bases on a positive proportion of primes, using two accepted corpus inputs. Its prime-modulus average-order corollary is weaker than the GRH asymptotic in Kurlberg–Pomerance, Theorem 2 ([primary paper](https://msp.org/ant/2013/7-4/ant-v7-n4-p08-s.pdf)); it does not address that paper's full integer-modulus theorem. Parent corrections replace an erroneous exceptional-set union equality with an upper bound and flag the opening density quantifier, novelty claim, and progression-only Artin reduction as unverified. Strict error budgets and the empty base set are included in the audit brief.

Decision: retain as a promising candidate and research record, without increasing the accepted substantial-finding count. A fresh T3-owned independent review round is running, with its task ID and full brief in `iteration2-arithmetic-r2-task.json`. The parent verification artifact is `../sources/i02_arithmetic/parent-source-verification.json`; finite reproduction output is `../experiments/i02_arithmetic_parent_checks.json`. QRH tuning and idoneal-number routes remain stopped proposals, not accepted universal obstruction theorems.

### Operator round 2 integration — 2026-10-08

The parent read the terminal result, full operator report and independent cross-field audit. It reproduced all original finite checks and the additional 16 exact cover checks, 10,240 reflection identities and 6,432 even-base logarithmic inequalities. All 19 manuscript files match their SHA-256 hashes, git-blob hashes and pinned tree entries; both literature PDFs match their recorded hashes. All six input hashes also match. The verification record is `../sources/i02_operator_r2/parent-verification.json`. These checks concern integrity and finite algebra; they do not establish universal proof or novelty.

The cross-field audit passes Proposition R and the necessary rank-two identities, with two useful precision points: the slope interval is compact, and Shangguan explicitly already proves the transversal threshold computation. Rank-two existence for the global operator remains unproved. Finite cyclicity of the individual fibres does not settle global cyclicity, and conditional similarity constructions preserve ordinary invariant subspaces.

The new operator report derives a global Gaussian decay estimate for the actual normalized backward intertwiner V. For the specified positive infinite-rank coupling T_a=S+M_a V it derives Gaussian decay, injectivity of both T_a and its adjoint, and absence of nontrivial invariant ideals. Every nonzero proper ordinary invariant subspace, if one exists, must therefore be a half-space. The parent checked the actual source recurrence, the two even-base drift identities, normalization, and the two-step kernel recurrences. The separate native independent audit in [i02-operator-r3.md](../reviews/i02-operator-r3.md) passes Sections 3–7, including explicit two-step kernel bounds and the global V estimate; it found no substantive correction. The finite-rank adjugate argument uses r≥1, with r=0 handled directly as F=0. None of these properties proves absence of ordinary invariant subspaces or establishes a substantial novel theorem.

Decision: retain round 2 as a research record; no increase to the accepted substantial-finding count. Round 3 must analyze actual ordinary invariant subspaces of this exact T_a, rather than repeat determinant identities or invariant-ideal arguments. Two idempotent attempts to create a fresh T3 child failed with `parent_not_active`; no new task was created. The failed launch brief is preserved in `iteration3-operator-halfspace-launch-failure.json`. A native subagent completed the independent audit of the new arguments. The original T3-owned operator child successfully accepted a distinct follow-up for ordinary invariant half-spaces; its accepted run receipt and original status handle are in `iteration3-operator-halfspace-resume.json`. Its assigned report is `i03-operator-halfspace.md`. This is a continuation of the existing delegated task, not a new top-level thread. The research objective remains open.

### Arithmetic round 2 integration — 2026-10-08

The parent read the completed independent review and checked the exact PD and splitting contracts. All 60 manuscript files match the immutable preprint tree and SHA-256 hashes; four literature downloads also match. The independent finite check reproduces 86,232 surviving base–prime instances with B=12, zero violations, and 2,430 independently computed orders. These are finite logic checks, not verification of the asymptotic or literature novelty. Evidence is in `../sources/i02_arithmetic_r2/parent-verification.json`.

The repaired theorem is now [R004](../findings/R004-simultaneous-bounded-index.md): simultaneous indices divide one fixed B(A,η) on a c*−η proportion of every sufficiently large prime dyad. Its prime-average corollary follows. The report now corrects the density quantifier, E3 union, strict error budget, 0.677 prior-art comparison and Kim attribution. The proposed Artin reduction using unspecified progression positivity is withdrawn. Full fixed-progression PD suffices by the review's union-of-classes argument, but is not supplied by the marginal PD theorem.

Decision: preserve R004 as one validated consequence with its own commit; do not count it as completion of the nonroutine-novelty objective. A fresh T3 round investigates fixed-progression PD. Its complete brief and task ID are in `iteration3-arithmetic-progressions-task.json`. The prior operator continuation failed at provider level after writing a candidate reflection proof; a fresh independent audit is running under `iteration3-operator-halfspace-r4-task.json`. The existing Hodge continuation still has pending work and was not duplicated.

### Operator rounds 3–4 integration — 2026-10-08

The fresh round-4 audit completed successfully. The parent read the full report and review, checked the actual pinned weight and normalization formulas, reproduced both finite test outputs, and verified all 18 manuscript files against the pinned tree and independent downloads plus both literature hashes. The original output reproduces byte-for-byte; the independent run adds 262,432 exact logarithmic identities and bounded noncommuting block models. The sole changed reviewer input was the shared iteration index. Evidence is in `../sources/i03_operator_r4/parent-verification.json`.

[R005](../findings/R005-operator-reflection-obstruction.md) closes the entire specified T_a=S+M_aV family as ordinary-ISP counterexamples: the plus and minus weighted-reflection spaces are closed invariant half-spaces, with zero intersection and dense nonclosed sum. The nonclosedness refinement uses the actual infinite normalizer's essential unboundedness. No substantive correction to the original half-space proof was needed. The historical provider failure has no bearing on this proof verdict.

Decision: commit this as one validated candidate obstruction, without increasing the substantial-new-finding count. A fresh T3 round analyzes ordinary invariant subspaces of the concrete asymmetric Q=S+RV, d_j=1 for j≤0 and 2 for j≥1. Its full brief and status handle are in `iteration4-operator-asymmetric-task.json`; report path is `i04-operator-asymmetric.md`. Gaussian decay, no invariant ideals, and failure of the old graph ansatz do not solve that new problem. The arithmetic progression round remains independent ongoing work; the overall research objective stays open.

### Arithmetic round 3 integration — 2026-10-08

The completed task proposes fixed-progression PD (AP), a new restricted two-sided correlation lemma (RC), and positive-lower-density primitive roots (A+) for every admissible integer base. The proposed new step inserts both physical endpoint residues before stripping shared labels and obtains the exact residual congruence by averaging one full shared prime interval. It does not infer conditional PD from the marginal law.

The parent read the full candidate and the actual general pairing, ideal-family, stripping, collision, multiplier, low-frequency endpoint, coefficient-transfer and quadratic-progression interfaces. The residue identity checks algebraically. All 60 pinned source files and five literature downloads match their hashes; all original author input/artifact hashes matched before integration. The complete finite output reproduces byte-for-byte, including 833,272 residue identities and the signed-base local checks. These checks certify neither analytic cancellation nor asymptotic conclusions. [Parent notes](../sources/i03_arithmetic_progressions/parent-preliminary-review.md) record the exact scope and correct a MathDB attribution unsupported by the parent's retrieved page.

Decision: preserve this as a candidate research record, not an accepted finding. A fresh T3-owned independent review audits §3 and the full extraction, with particular attention to shared-label conditioning, enlarged Fourier arcs, parameter order and absolute-error assertions. Its task ID and full brief are in `iteration3-arithmetic-progressions-r4-task.json`. AP and A+ remain unaccepted until that verdict is integrated; no new substantial-finding count is recorded. The operator asymmetric task continues independently.
