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

## Iteration 02 — running

| Lane | Work | Intended report |
|---|---|---|
| Cross-field, round 1 | Returned failed sunflower/Kakeya bridges and a proved rank-one perturbation obstruction; no substantial new target case. Independent proof audit is running. | [Report](i02-crossfield.md) |
| Operator construction, round 2 | Audit cross-field arguments; solve or obstruct the exact rank-two transfer identities using the accepted operator's dyadic weights, and analyze actual invariant subspaces. | `i02-operator-r2.md`; `../reviews/i02-crossfield-r2.md` |
| Arithmetic, round 1 | Returned a positive-proportion bounded-index candidate combining PD(p−1) and uniform Hecke zero-freeness. Finite checks and source hashes reproduce; independent proof/novelty review is running. | [Report](i02-arithmetic.md) |
| Arithmetic, round 2 | Audit the uniform splitting estimate, density quantifiers, prime-modulus average-order corollary, claimed Artin reduction, and primary prior art. | `../reviews/i02-arithmetic-r2.md` |
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
