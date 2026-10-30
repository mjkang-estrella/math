# Independent T298P scoped Lean review, round 2

Verdict: **PASS for the stated scoped support package**. Required findings: **none**. This verdict concerns four finite-dimensional/scalar support declarations and four concrete scalar controls. It does not certify the analytic T298P theorem, acceptance, novelty, or count credit. This is a fresh review after the prior provider OOM; no prior verdict was inherited.

The unchanged analytic target is exactly two bounded self-adjoint elements in a faithfully normally tracial von Neumann algebra with
`-infinity < chi(Z1,Z2) < chi*(Z1,Z2) < infinity`, using the original operator-norm-cutoff ordinary-limsup microstates entropy. Neither supplied matrix-unit conditioning nor an ultrafilter replaces it. No declaration in the package states that theorem.

## Inputs and independence

Read the complete assignment brief, repository AGENTS, pinned-upstream metadata/catalogue, frozen r104 candidate and scope, all Lean source, build and integrity-checker source, lake configuration, coverage, binding, provenance, portability and validation receipts/types. The independently checked author MANIFEST anchor is `e8d1d16e4d90b53b9fbb2b469a40e63c1d8b1e67b3647448f37f33b0b1857400`. The r104 candidate/scope/manifest digests are recorded in `binding.json` and independently rechecked by this packet's verifier.

No author, candidate, shared-index, or source file was edited. Only this review directory and temporary compiler workspaces were written. No network, browser, upload, nested agent, staging or commit was used. The parent supplied the task and prior-failure context; its build and other review conclusions were not used as evidence for this verdict. This review makes no new analytic deduction from the pinned source theorem and does not audit upstream truth.

## Exact support coverage and correspondence

| Declaration | Checked statement and limits |
|---|---|
| `T298P.coefficient_isometry` | For arbitrary finite `Q,A`, a real inner-product space `E`, real coefficients `C`, arbitrary vectors `xi`, and the **complete column Gram premise** `sum_q C(q,a)C(q,b)=delta(a,b)`, proves `sum_q ||sum_a C(q,a) xi(a)||² = sum_a ||xi(a)||²`. No orthogonality of `xi` is assumed. Expanding the real inner product preserves every cross term; exchanging finite sums and using the Gram premise removes them. The proof was read independently. |
| `T298P.leading_score_energy` | Under the same premise, for all **real** epsilon and k, proves the scaled norm sum is `sum_a ||xi(a)||²/(epsilon²*k⁴)`. Norm scaling squares `1/(epsilon*k²)`, hence k⁴. This supports the abstract leading-score norm calculation in candidate §3/equation (3). It does not instantiate the actual matrix coefficients, normalized matrix trace or conjugate variables. |
| `T298P.gap_transfer` | Eleven finite real variables, explicit nonnegative coefficient/errors, endpoint `micro1 <= star1`, microstates increment lower bound, and nonmicrostates increment upper bound imply `c*(g0-g1)-(eMicro+eStar) <= star0-micro0`. Here `gi=sourceStari-sourceMicroi`. Subtracting the two increment inequalities and adding endpoint comparison gives exactly this sign. This is the finite-real rearrangement of candidate §§4–5, conditional on its analytic increments. |
| `T298P.strict_gap` | Adds `c>0`, positive source gap, noisy source gap at most half the original gap, and **strict** total-error bound `< c*g0/2`; concludes `micro0 < star0`. The transferred lower bound is at least `c*g0/2-errors>0`. Candidate applications set c=k⁻² and must separately supply all hypotheses. |

`gap_transfer` does not need its three nonnegativity assumptions for the linear rearrangement; the source marks them with underscore names. `strict_gap` carries a redundant explicit source-gap positivity premise, also underscore-marked. These are stronger interfaces with harmless redundant premises, not hidden hypotheses or weakened conclusions.

Every entropy variable is `ℝ`, not an extended real or entropy function. There is no hidden construction/existence theorem, finite-entropy proof, or limsup/liminf operation in the formal statements. Empty finite index types are allowed; when A is nonempty and Q empty the Gram premise is inconsistent, but the general theorem is not vacuous. The independent nonzero Fin-2 example below supplies the premise concretely. Lean real division is total: at epsilon=0 or k=0, both sides of `leading_score_energy` are zero. This is an algebraic boundary convention; the candidate applies it only with positive epsilon and positive integer k.

## Author controls: assignments and sensitivity

All four original controls are valid kernel-proved concrete inequalities. For the last three, c=1 and unmentioned errors are zero. The assignments below remove ambiguity from their compressed expressions. Output tuple order is `(micro0,micro1,star0,star1)`; source order is `(sourceMicro0,sourceMicro1,sourceStar0,sourceStar1)`.

| Control | Concrete interpretation |
|---|---|
| `wrong_normalization` | epsilon=1, k=2 and unit source energy: the squared scale is 1/16, whereas replacing k⁴ by k² gives 1/4. Both are nonzero. |
| `missing_comparison` | Output `(0,1,0,0)`, source `(0,1,1,1)`. Both increment bounds hold, source gaps are 1 and 0, but endpoint comparison is false and the claimed transferred lower bound 1<=0 fails. |
| `wrong_gap_sign` | Output `(1,0,0,0)`, source `(1,0,1,1)`. Endpoint and both increments hold. Source gaps are 0 and 1; the correct transferred inequality is -1<=-1, while the reversed-sign claim is 1<=-1 and fails. |
| `equality_errors_not_strict` | Output `(0,0,0,0)`, source `(0,1,2,2)`, eMicro=1, eStar=0. Endpoint and increments hold, g0=2, g1=1, and error equals c*g0/2. Strict output inequality fails. Thus merely non-strict absorption cannot prove strict separation. |

The controls demonstrate scalar normalization/sign/hypothesis sensitivity, not the analytic correctness of the Fisher construction or entropy increments. In particular they are not attempts to derive false universal statements from inconsistent premises.

## Fresh compilation, additional examples and mutation controls

First replayed the inspected author runner from `copied-author/` with explicit compiler and cache locations and new output `fresh-build/`. It copied source into a temporary directory, generated new support/control oleans, and checked all eight theorem types and axioms. All three steps passed without warnings; logs match the author's recorded logs byte-for-byte. Source SHA256 values match the frozen source. This is independently executed evidence, not the parent's replay.

Then independently implemented `audit.py` and compiled **new copies** of both author modules plus `Independent.lean` in another temporary directory. Four successful steps and five expected failures are recorded in `independent-build/receipt.json`; full type/axiom output is `independent-build/types-axioms.log`. All 18 theorem declarations (8 author, 10 reviewer) report only `propext`, `Classical.choice`, and `Quot.sound`. Source inspection found no custom axioms, sorry/admit, unsafe escape, or native decision shortcut. The regex source scan is supplemental; the literal source and elaborated types/axiom dependencies were inspected too.

The new examples use rational orthogonal coefficient matrix `[[3/5,4/5],[-4/5,3/5]]` and real vectors xi=(1,2), whose cross inner product is 2. They prove the full column Gram premise, energy 5 despite nonorthogonality, and scaled energy 5/144 at epsilon=3,k=2. The all-ones coefficient matrix changes energy to 18 instead of 5, demonstrating the Gram premise matters. A zero-epsilon example checks the total-division convention explicitly.

The strict-gap theorem is instantiated with c=1, eMicro=eStar=1/8, output `(0,7/8,3/4,7/8)` and source `(0,1,2,2)`. All hypotheses are proved by exact arithmetic before obtaining `0<3/4`; this tests nonvacuity and the theorem's argument interface. Additional conjunctions explicitly check the endpoint, sign and weak-error counterexamples.

Five copied-source mutations are expected to fail compilation: k⁴ changed to k²; the column-Gram premise removed from the isometry; endpoint comparison removed from gap transfer; source-gap difference reversed; and strict error absorption weakened to <=. Logs show substantive unsolved algebra/inequality goals, not missing imports or unknown identifiers. Their failure alone would not establish falsity; the independent concrete counterexamples and the original normalization control supply that evidence. Negative source files are deliberately false test inputs and are not claimed as formal results.

During reviewer-example development, a trial strict-gap endpoint assignment did not satisfy its upper increment bound, and an unused binder triggered a warning. That attempted build was rejected. The fixture was corrected to the assignment above and the binder renamed. `development-attempt-1/Independent.log` preserves the diagnostic; this was not a defect in the author source. The final independent source builds without warnings.

## Portability, integrity and trust boundary

The copied source works with explicit `--lean` and `--cache`; neither runner needs its source to remain in the author's directory or downloads dependencies. The pinned compiler reports Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; its executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Mathlib is pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`, and all nine dependency Git revisions and tracked-source cleanliness were checked. Complete revisions are in both receipts.

This trusts the installed compiler/runtime and pre-existing dependency oleans. Neither mathlib nor the compiler was rebuilt. Git HEAD/cleanliness does not establish that cached oleans were produced from those source revisions, and hashing the executable does not authenticate the whole compiler installation or shared libraries. Fresh author/reviewer oleans were built; dependency oleans were reused. No broader bootstrap/security assurance is inferred.

The inspected author `verify.py` checks an externally supplied manifest hash, exact file membership and digests, bound-reference digests, recorded status/source/log consistency, eight recorded axiom entries and their permitted names. It does **not** execute Lean or prove the receipt truthful; its source/axiom-name scans are not general theorem-environment audits. Its file inventory ignores empty directories, and it does not independently authenticate external compilers/caches. These limits are accurately distinguished from fresh compilation in the author README. The fixed manifest anchor binds the exact inspected source, so these are no required defects for this packet.

This review's `verify.py` likewise performs a read-only integrity/receipt check, not compilation. It requires the separately supplied review MANIFEST SHA256, checks every payload file and rejects symlink entries, checks author payload identity against the fixed author anchor, rechecks all bound references, ties compiled-source and log digests to the two fresh receipts, and checks the exact 8/18 declaration-name sets and five expected-rejection steps. The verifier and audit runner are included in the manifest. An external trusted anchor is essential; a self-consistent altered packet is not authenticated by its own manifest.

## Analytic debts and findings

Unformalized: the source tuple and its finite entropy gap; construction of exactly two bounded self-adjoint operators and faithful normal trace; the actual real coefficient Gram/trace normalization; matrix-unit/tangent/coarse-bimodule geometry; normal-bundle injectivity, uniform inverse and Jacobian bounds; arbitrary-size original-limsup volume recovery and matched constants; conjugate-variable domains, adjoints, inner derivations, Neumann series and projection; the Fisher remainder estimate; exact free-noise laws and entropy integration; relative microstates change of variables and all-size conditioning models; the two entropy increment estimates; endpoint chi<=chi*; Gaussian asymptotics, selection of noise/epsilon, finite-entropy bounds and liminf passage. The Lean declarations prove none of these analytic interfaces and cannot establish the frozen target without them.

Required changes: **none for scoped support**.

Optional polish: label the scalar assignments explicitly in the author's controls/coverage (the table above supplies them for this review), and rename the inherited lake-manifest root `name` from `t224g_scoped_support` to `t298p_scoped_support` if desired. The direct pinned-compiler runner does not use that stale metadata name, so no build or mathematical defect follows. The separately reported proof-review prose omission of `1/(epsilon²*k⁴)` is outside this frozen Lean packet; candidate equation (3), its displayed leading-score identity and this formal declaration all contain the correct factor.

No claim of a new-to-literature theorem is made. This is independent scoped verification of finite coefficient algebra and real inequality absorption only, with no acceptance or count change.
