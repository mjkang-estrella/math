# Independent review: MathDB 370245 / Schur stability

**Verdict: PASS on mathematics, source matching, and formal verification. Eligible for ONE campaign outcome covering both P and R, subject to the parent's separate PDF QA and release steps.** This verifies a known specialization of Shivam Patel's posted counterexample family. It is not a discovery, a new-to-literature theorem, or evidence of formalization priority. No mathematical or formal proof gap was found. Minor artifact issues are listed below.

Reviewed on 2026-10-25. Candidate directory:

`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-campaign/outcomes/schur-stability`

## Scope and exact bytes

I read `openai-proof-research/AGENTS.md`, the upstream revision record, and the manuscript catalogue. No mathematical result from the pinned OpenAI repository is used here. I read the complete candidate `main.tex`, `PROOF.md`, and `formal/SchurStability.lean`, as well as the metadata, outcome, source, README, and self-review records. I also read the full primary-paper HTML, including its application and proof sections, and the actual frozen MathDB statement and Patel reply; I did not substitute their summaries for the primary evidence.

The canonical files independently reviewed and compiled have these SHA-256 hashes:

| File relative to candidate | SHA-256 |
| --- | --- |
| `formal/SchurStability.lean` | `1c9c3eb6834dfdb0ae068e822e689415aa472fbe7677b97fea28327b9e4d516d` |
| `main.tex` | `4c5e3e37096111ea97c06ff445347065f0142fce55bf9e79f78c973957c7d722` |
| `PROOF.md` | `0fa008410ad3b6e7c3c03b537d74c76a0a322013daf406f10299726780a7159c` |

The hashes were rechecked after compilation. This review attaches to those bytes, not to a sibling build copy or an earlier paper hash.

Primary evidence is in `openai-proof-research/frontier/campaigns/2026-10-25/schur-stability-lane/sources/`:

| Frozen source | SHA-256 |
| --- | --- |
| `stability-2509.06715v1.html` | `935b1b6b0a79394ddf07bd6d3044ea46a4c7352afc694589341d1f9d66b72795` |
| `370245.json` | `2382452bb7f6292782283d06b16ae6b57dd4760d484a500d2465d6c08b6a88e1` |
| `stability-source.json` | `87afacf2d9dd785f1db941bcca101746f01deea85d1f0af203a2f67e7436d267` |
| `stability-brief.md` | `b140355049eb0d2b5fab3f8abb55e469e336635c1b7ca0e424b086b249bcb8f0` |

The HTML identifies Banerjee and Chaudhury, *On the Schur Stability of Some Image Reconstruction Operators*, arXiv:2509.06715v1, 8 September 2025. The MathDB record is number 370245, UUID `3d562280-0003-4324-bbd0-3dccec634fd1`. Patel's actual reply is number 1, UUID `5a30dc24-61b4-49cc-a6de-ee5f67a71bf3`, posted `2026-08-20T21:22:41.195834Z`, attributed to Shivam Patel / `shivampatel`.

## Exact source interpretation

The introduction defines stochastic to mean **row-stochastic**: nonnegative entries and `We=e`. Primitivity means one positive power has every entry strictly positive. The Perron vector is a positive left eigenvector, normalized there by `pi^T e=1`. The source works in real finite dimension at least one and computes spectra in the complex sense.

Equations (1) and (2) are precisely

`P(t)=W(I-tB)` and `R(t)=I-W+(I+tB)^(-1)(2W-I)`.

Conjecture 1.1 (`S1.Thmconjecture1`) requires primitive stochastic W, positive-semidefinite B, the componentwise upper bound `Be <= rho(B)e`, and `pi^T Be > 0`. Its conclusion is strict Schur stability of **each** operator for **every** `0<t<2/rho(B)`. The exact MathDB statement agrees.

There is no additional entrywise nonnegativity hypothesis on B in this conjecture. The paragraph immediately preceding it explicitly explains that nonnegativity is not essential. Example 1.2 (`S1.Thmexample2`) gives `B2=(1/10)[[4,-1],[-1,2]]` and explicitly places it under the conjecture's assumptions. The abstract's nonnegative setting, Corollary 1.2, and the application-specific nonnegative matrices in Section 2 do not narrow the displayed conjecture. In particular, `Be>=0` is not required: it appears in a separate corollary. Thus the candidate's negative off-diagonal entries and negative second coordinate of Be are allowed.

The ambient setup calls B nonzero and assumes the inverse exists where R is evaluated. Both are satisfied explicitly here. The witness does not need W symmetric, doubly stochastic, positive semidefinite, or obtained from the kernel-denoiser construction in Section 2. It refutes Conjecture 1.1 as stated, not a narrower conjecture restricted to that application class.

## Independent mathematical audit

The literal witness is

```text
W  = [[0, 1], [1/4, 3/4]]
B  = (1/11) [[9, -4], [-4, 3]]
pi = [1/5, 4/5]^T
t  = 1.
```

I independently recomputed the products, traces, determinants, and weighted row sums using Python's exact `fractions.Fraction`, in addition to inspecting the proofs and compiling Lean.

| Requirement | Verification and corresponding Lean declarations |
| --- | --- |
| Correct dimension, real entries, all-ones vector | `Mat` is `Matrix (Fin 2) (Fin 2) ℝ`; `e=![1,1]`; all divisions are in ℝ, not integer arithmetic. The literal data agree with the paper and Patel specialization. |
| Row-stochastic W | Entries are nonnegative and row sums are one; `W_stochastic`. `W_fixes_e` also verifies `We=e`. |
| Primitive W | `W²=[[1/4,3/4],[3/16,13/16]]`, all strictly positive; `W_square`, `W_primitive`, with positive exponent 2. |
| Genuine positive left Perron vector | Both pi coordinates are positive and sum to one; `pi_positive`, `pi_normalized`. Direct left multiplication gives `pi^T W=pi^T`; `pi_stationary`. The complete W spectrum is `{1,-1/4}`, so its actual radius is one; `pi_is_left_Perron` identifies the eigenvalue with `realRho W`, not merely an arbitrary stationary value. |
| B positive semidefinite | `B_hermitian` proves real symmetry. `B_quadratic` proves `11 x^T Bx=8(x0-x1/2)^2+x0^2+x1^2`. For nonzero x the last two squares have positive sum. `B_posDef` uses the standard mathlib positive-definite predicate, and `B_posSemidef` derives the standard positive-semidefinite predicate. This is stronger than required. |
| Nonzero B and its radius | B has entry `9/11` and eigenvalue one, so it is nonzero. Its complete complex spectrum is `{1,1/11}` and actual radius is one; `B_char_det`, `B_spectrum`, `rho_B`, `realRho_B`. |
| Componentwise source bound | `Be=[5/11,-1/11]^T <= [1,1]^T=rho(B)e`; `B_e`, `B_e_le_e`, `B_source_bound`. This is an upper bound, not an absolute-value bound or an unmentioned positivity requirement. |
| Strict Perron-weighted positivity | `pi^T Be=(5-4)/55=1/55>0`; `pi_B_e`, `pi_B_e_positive`. |
| Strict admissible step | `t=1`, `rho(B)=1`, and `0<1<2`; `strict_step`. Neither endpoint of the allowed interval is used. |
| Actual source P | `P A D s=A*(1-s•D)`. `P_exact` yields `[[4/11,8/11],[7/22,7/11]]`, with the source's multiplication order. |
| Actual source inverse and R | `J=[[7/12,1/6],[1/6,5/6]]`. Both `J(I+B)=I` and `(I+B)J=I` hold (`inverse_left`, `inverse_right`). `actual_inverse` uses `Matrix.inv_eq_left_inv`, thereby identifying the real matrix inverse operation itself. `R A D s=1-A+(1+s•D)⁻¹*(2•A-1)`, and `R_exact` yields `[[1/2,1/4],[0,1]]`. |
| Both strict stability claims fail | The complete spectra are `sigma(P)={0,1}` and `sigma(R)={1/2,1}`. Both actual spectral radii equal one. This violates `<1`, even though neither radius needs to exceed one. |

For clarity, `J(2W-I)=[[-1/2,5/4],[1/4,3/4]]`, so adding `I-W` gives exactly the displayed R. The inverse is not silently replaced by a formal symbol or defined to be the desired answer. The polynomial coefficients independently checked are:

```text
W: z² - (3/4)z - 1/4 = (z-1)(z+1/4)
B: z² - (12/11)z + 1/11 = (z-1)(z-1/11)
P: z² - z = z(z-1)
R: z² - (3/2)z + 1/2 = (z-1)(z-1/2).
```

The paper and PROOF.md correctly present these identities and the sum-of-squares argument. No numerical approximation, unproved spectral inequality for products, perturbation theorem, or statement from the source paper's other proofs is needed.

## Spectral semantics and type conversions

The formalization has a complete bridge to library spectral radius; it does not define rho by a hand-picked maximum of two claimed eigenvalues.

1. `complexify` is entrywise `algebraMap ℝ ℂ` on the actual real matrix. Thus rational entries retain their values, and the computed spectra concern the complexification of the source operators.
2. `spectrum_iff_det_zero`, for arbitrary `A : CMat` and `z : ℂ`, rewrites mathlib spectrum membership using `spectrum.mem_iff`, `Matrix.isUnit_iff_isUnit_det`, and the field criterion for units. The scalar matrix is `algebraMap ℂ CMat z`, i.e. `zI`, with the correct diagonal embedding. This gives `z ∈ spectrum ℂ A` iff `det(zI-A)=0`.
3. All four `*_char_det` theorems quantify over **every complex z**. The four `*_spectrum` theorems are biconditionals, so they both include the listed values and exclude all unlisted complex values. There is no missing reality-of-eigenvalues assumption.
4. `eigenvalue_iff_spectrum` uses `Matrix.toLinAlgEquiv'` on the two-dimensional complex vector space and mathlib's finite-dimensional `Module.End.hasEigenvalue_iff_mem_spectrum`, followed by `AlgEquiv.spectrum_eq`. The matrix acts by column multiplication. `P_complex_eigenvector` and `R_complex_eigenvector` use the standard `HasEigenvector` predicate, including nonzero-vector proofs by their first coordinates 8 and 1. The resulting `P_hasEigenvalue` and `R_hasEigenvalue` are standard library eigenvalue assertions.
5. `rho A` is literally `spectralRadius ℂ (complexify A) : ℝ≥0∞`. I inspected the pinned library definition: it is the supremum of scalar nonnegative norms over the quasispectrum. `spectralRadius_eq_of_unital` identifies this with the supremum over the spectrum in this unital matrix algebra. The additional zero in the quasispectrum does not alter the supremum.
6. `radius_eq_one` proves an upper bound on **every** spectral value using the complete-spectrum biconditional, and the lower bound from actual membership of `1`. Its `exact_mod_cast` moves `‖c‖₊ <= 1` from NNReal into ENNReal; it does not change a complex absolute value into an unrelated quantity. The secondary values `1/11`, `-1/4`, `0`, `1/2` have respective norms at most one. Hence `rho_B`, `rho_W`, `rho_P`, and `rho_R` prove exact ENNReal equalities to one.
7. `realRho A=(rho A).toReal` is only used for source bounds and the real formulation after the relevant radius-one equality is established. There is no conversion of infinity to a spurious real zero in this witness. `realRho_B`, `pi_is_left_Perron`, `realRho_P`, `realRho_R`, and the real instability theorems certify the needed finite conversions. Strict Schur stability itself is also directly negated in ENNReal.

The standard `Matrix.PosDef`/`PosSemidef` predicates include Hermitian symmetry and quadratic-form positivity; their finite-support formulation agrees with ordinary quadratic forms on `Fin 2`. The standard constructor used in `B_posDef` handles that conversion. Natural-number `2•A` in R is repeated addition and agrees with multiplication by the real scalar 2. Real scalar multiplication `s•D` is entrywise, and matrix `1` is the identity. No overloaded operation changes a source operator.

`SourceHypotheses` faithfully bundles the normalized dimension-two assumptions. `ConjectureP` and `ConjectureR` are dimension-two restrictions, not claims to have encoded an arbitrary-dimension theorem. Normalizing pi imposes a harmless positive scaling, already consistent with the source's convention; a counterexample satisfying this stronger normalization also satisfies the unnormalized version. `source_hypotheses`, `strict_step`, and the two instability theorems instantiate the universal statements separately. `both_conjectures_false` proves both negations. `schur_counterexample` also packages the source assumptions and both failures explicitly. Since dimension two is allowed by the source, this suffices to refute the unrestricted conjecture. The generic wrappers need not establish finiteness of `realRho` for every hypothetical matrix to make this explicit finite witness valid.

## Independent compilation and axiom audit

I did **not** run the supplied verifier: it writes build products and invokes git, both excluded by this assignment. I independently passed the full canonical source text, followed by `#check` and `#print axioms` for every local `abbrev`, `def`, `theorem`, and `lemma`, directly to:

```text
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true --stdin
```

The process working directory was `/tmp`. `LEAN_PATH` was replaced with only the nine pinned dependency `.lake/build/lib/lean` directories under:

`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`

The candidate imports only `Mathlib`. No candidate directory or sibling build directory was placed on the search path. No candidate `.olean` was imported, no `-o` option was supplied, and no Lean source/check/log/object file was written. The full source, rather than `import SchurStability`, was the stdin input.

Observed result:

```text
Lean (version 4.34.1, x86_64-unknown-linux-gnu,
      commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
exit code: 0
local declarations: 77 = 2 abbrev + 17 def + 58 theorem + 0 lemma
local instance declarations: 0
successful #check commands: 77
matched #print axioms reports: 77 / 77
axiom union: Classical.choice, Quot.sound, propext
warnings/errors: none
forbidden proof tokens (sorry/admit/native_decide/axiom/unsafe): none
```

Every axiom report matched the declaration inventory; no axiom report or definition was omitted. There are no local instances requiring an extra generated-name audit. The reports agree with the candidate's claimed 77-declaration count, but this conclusion comes from a new full-text run, not the supplied `build/audit.json` or existing `.olean` files.

For reproducibility, the essential in-memory invocation was equivalent to the following (run from the workspace root; no file writes):

```python
from pathlib import Path
import os, re, subprocess

root = Path('/home/mj-kang/Documents/Dev/math')
campaign = root / 'openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-campaign'
source = campaign / 'outcomes/schur-stability/formal/SchurStability.lean'
packages = root / 'openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages'
deps = ['mathlib', 'plausible', 'LeanSearchClient', 'importGraph',
        'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli']
text = source.read_text()
names = re.findall(r'^(?:noncomputable )?(?:abbrev|def|theorem|lemma)\s+(\w+)', text, re.M)
assert not re.findall(r'^.*\binstance\b.*$', text, re.M)
checks = '\n\n' + '\n'.join(
    f'#check SchurStability.{n}\n#print axioms SchurStability.{n}'
    for n in names) + '\n'
env = dict(os.environ, LEAN_PATH=os.pathsep.join(
    str(packages / n / '.lake/build/lib/lean') for n in deps))
result = subprocess.run(
    [str(root / 'dlp-research/.tools/lean-4.34.1-linux/bin/lean'),
     '-DwarningAsError=true', '--stdin'],
    input=text + checks, text=True, capture_output=True, cwd='/tmp', env=env)
assert result.returncode == 0, result.stdout + result.stderr
reports = re.findall(
    r"'SchurStability\.(\w+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
    result.stdout, re.S)
assert len(names) == 77
assert sorted(n for n, _ in reports) == sorted(names)
observed = {a.strip() for _, values in reports for a in values.split(',') if a.strip()}
assert observed == {'propext', 'Classical.choice', 'Quot.sound'}
```

I separately read dependency HEAD/ref files without invoking git and verified that they match the campaign pins:

| Dependency | Revision |
| --- | --- |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` |

This establishes the selected dependency revisions, not an independent rebuild or clean-tree audit of the dependencies' existing library object files. Such upstream dependency trust is distinct from the specifically excluded use of local candidate objects.

## Attribution, counting, and limits

Patel's reply contains the same B and the family `v=1/(5-s)`, `W_s=[[0,1],[v,1-v]]`, `pi_s=[v,1]^T/(1+v)`, for `0<s<2`. Substituting `s=1` gives `v=1/4`, the exact W and pi above, and the posted boundary choice `t=s` gives `t=1`. The candidate's attribution is accurate. This is not the reply's separate numerical `t=4/5`, `W21=7/30` example, nor a claim to formalize the full parameter family.

The known-family relationship is exact, not a superficial resemblance. The independent contribution here is verification and formalization of that specialization. The full family's claims of radii greater than one beyond its threshold, or arbitrarily small thresholds, are not proved by this module and are not needed for its verdict. The paper appropriately distinguishes them.

Both P and R fail simultaneously for the same admissible data and same step. **Count one verified outcome for MathDB 370245, not two outcomes for its two operator conclusions.** The result is eligible as a verified refutation/formalization of a known posted claim; it is not eligible as a newly discovered mathematical result. It does not refute the paper's sufficiently-small-step theorem, its symmetric/doubly-stochastic results, its diagonal-B case, or its `B=alpha I+beta E` case. The witness is nonsymmetric, not doubly stochastic, and outside those special B classes.

## Remaining gaps and minor artifact issues

**Mathematical/formal gaps: none found for the stated concrete counterexample and both source conclusions. No unpaid spectral-radius, inverse, PSD, Perron-vector, or type-conversion bridge remains.**

The following are release/documentation issues, not defects in the proof:

1. `metadata.json` retains historical lane artifact entries. Its `artifact_sha256["paper/main.tex"]` is `2d19c4cb291bad0f30cf7e7617533226b54d06aedff7cbce52b89446d7e426d1`, whereas the reviewed candidate `main.tex` has hash `4c5e3e37096111ea97c06ff445347065f0142fce55bf9e79f78c973957c7d722`. Its `PROOF.md` hash is `7258d03c6337a4ce2735aee4053d6b14c74f1f77fcc8ddfb8e786b5d2de0c865`, whereas the candidate's is `0fa008410ad3b6e7c3c03b537d74c76a0a322013daf406f10299726780a7159c`. The README explains historical lane paths, but these should be explicitly separated from current release hashes or refreshed at release. The Lean hash is current and matches the independent run.
2. The reproduction command in `PROOF.md` and `main.tex`, `python3 verify_outcome.py .`, applies to an assembled release containing that script. The current candidate directory does not contain it; the README correctly gives the campaign-checkout alternative `../../verify_outcome.py`. Clarify this distinction consistently. It did not obstruct the independent stdin verification.
3. Review status fields in `outcome.json`, `metadata.json`, and the prose remain pending/candidate, and historical PDF/page-inspection metadata cannot certify the exact final release bytes. The parent should integrate this review, perform its assigned PDF QA, and bind final paper and release hashes to that QA. I did not build, render, or visually inspect a PDF, and make no PDF-layout approval claim.

No nested agents were started, no git command was invoked, and no build or release output was written. The only file written by this review is `campaignreviews/schur-stability.md`.

## Parent integration addendum

The review was moved from the reviewer's `campaignreviews/` location into this campaign's `reviews/` directory. The parent clarified that the verifier command applies to an extracted release and relabeled historical lane artifact hashes in metadata. No mathematical statement or Lean proof changed. The final paper's TeX hash is `cac2bb3b86a204b598ae4a2ed63180b5364941c376397a4ea7a80216a544c60c`; all four rendered pages, including the clarified reproduction paragraph, were visually inspected.
