# Candidate: negative-order Vendi–LCR dominance without full rank

Status: proposed complete mathematical proof of the remaining singular negative-order case; independent source/novelty review and full matrix Lean bridge pending. No count assigned. The positive-order comparison is already proved in the latest primary source and is not new.

## Exact source and remaining scope

Phuc Nguyen, Josiah Couch, Rahul Bansal, Alexandra Morgan, Chris Tam, Miao Li, Rima Arnaout, and Ramy Arnaout, *Which Similarity-Sensitive Entropy (Sentropy)?*, arXiv:2511.03849v4 (30 March2026): <https://arxiv.org/html/2511.03849v4>. Current arXiv abstract and complete history were checked; v4 is latest. Local exact HTML is `sources/2511.03849v4.html`. A public primary PMC copy is <https://pmc.ncbi.nlm.nih.gov/articles/PMC12642762/>.

Original v1 Conjectures1–2 / MathDB371345–371346 compare Vendi score and Leinster–Cobbold–Reeve diversity for every real order. **Latest v4 Theorem1 already proves every q≥0, and q<0 when Z is full rank.** Its abstract, theorem statement, SectionIII Case5, and discussion retain that full-rank restriction. Those old cases are excluded from this candidate.

Let Z be a real symmetric positive semidefinite n×n matrix, n>0, with Zii=1 and0≤Zij≤1. Write Ri=Σj Zij≥1 and λ1,...,λn≥0 for eigenvalues. The Vendi convention discards zero eigenvalues: the source's archived implementation explicitly selects eigenvalues e>0 before computing powers. Thus for finite q≠1,

\[
 \operatorname{VS}_q(Z)=\left(\sum_{\lambda_j>0}(\lambda_j/n)^q\right)^{1/(1-q)},\qquad
 D_q(Z,1/n)=\left(\frac1n\sum_i(R_i/n)^{q-1}\right)^{1/(1-q)}.
\]

For q<0, the comparison is equivalent to

\[
 \sum_{\lambda_j>0}\lambda_j^q\ge\sum_iR_i^{q-1}.
\]

Zero eigenvalues are omitted, not assigned an infinite negative power. This support convention is essential. Epsilon-regularization of a singular Z would diverge for negative q and would not prove the asserted finite support inequality.

## Proposed stronger inequality, valid for every finite real q<1

Define Ei=Σj Zij²=(Z²)ii. Then

\[
 \boxed{\sum_{\lambda_j>0}\lambda_j^q
 \;\ge\;\sum_iE_i^{q-1}
 \;\ge\;\sum_iR_i^{q-1}.}
\]

The positive-order overlap with the existing source is background; the new application under review is q<0 with arbitrary rank.

Choose an orthonormal eigenbasis u1,...,un. For each row i define weights on the positive spectrum by

\[
 w_{ij}=\lambda_j|u_j(i)|^2\quad(\lambda_j>0).
\]

They are nonnegative and sum to Zii=1. Their weighted mean of the eigenvalues is

\[
 \sum_{\lambda_j>0}w_{ij}\lambda_j
 =\sum_j\lambda_j^2|u_j(i)|^2=(Z^2)_{ii}=E_i\ge1.
\]

The function x↦x^(q−1) is convex on(0,∞) for q<1. Scalar weighted Jensen, applied separately at each row, gives

\[
 E_i^{q-1}
 \le\sum_{\lambda_j>0}w_{ij}\lambda_j^{q-1}
 =\sum_{\lambda_j>0}\lambda_j^q|u_j(i)|^2.
\]

Sum over i and use Σi|u_j(i)|²=1 to get the first inequality. Since each0≤Zij≤1, Ei=Σj Zij²≤Σj Zij=Ri. The exponent q−1 is negative, so Ei^(q−1)≥Ri^(q−1), proving the second inequality.

Multiplication by n^(−q)>0 and taking the positive power1/(1−q) prove VSq≥Dq for every finite q<0 with no full-rank assumption.

## Order minus infinity

Let λmin be the smallest positive eigenvalue. Each Ei is a convex combination of positive eigenvalues under the weights above, so λmin≤Ei≤Ri for every i. Consequently

\[
 \operatorname{VS}_{-\infty}(Z)=n/\lambda_{\min}
 \ge n/\min_iR_i=D_{-\infty}(Z,1/n).
\]

Together with latest-source Theorem1 this mathematically supplies the entire original order range. Any Lean claim must state exactly which part is formalized; the known positive-order theorem is not silently treated as a new axiom.

## Weighted-distribution extension, the same candidate

The same proof extends beyond uniform p. For strictly positive probabilities pi summing to1, put A=diag(sqrt(p)) Z diag(sqrt(p)), whose eigenvalues sum to1, and ri=(Zp)i. The row weights λj|uj(i)|²/pi sum to1. Their mean is (A²)ii/pi=Σj pj Zij²≤ri. Multiplying each row's Jensen inequality by pi yields

\[
 \sum_{\lambda_j>0}\lambda_j^q
 \ge\sum_i p_i\left(\sum_jp_jZ_{ij}^2\right)^{q-1}
 \ge\sum_i p_i(Zp)_i^{q-1}\quad(q<1).
\]

This is one strengthening of the same support comparison, not an additional discovery count.

## Prior-art boundary

Scalar Jensen, spectral decomposition, and matrix power inequalities are classical and are not claimed new. The latest source has an explicit unresolved singular negative-order gap, but that alone does not demonstrate novelty. Independent review must determine whether an older general trace/diagonal-moment inequality already states this exact stronger bound, and must search current Vendi/LCR literature for a prior comparison. No costly matrix formalization or discovery credit should precede that check.

## Complete new trace/row theorem in Lean

The finite positive-spectrum Jensen argument and its canonical actual-matrix bridge now compile warning-free using the pinned Lean4.34.1. The exact full PSD hypothesis is used; no supplied spectral decomposition or full-rank assumption remains.

- `formal/VendiJensen.lean`: SHA256 `4b23c4d70250186b98725b4015aa700392753ff2f56cff7fe8cc967b5da942df`.
- `formal/VendiMatrix.lean`: SHA256 `7dc44262b3fb7e8a711eb73af3d742790581c61f6cfe39a4657418cbb14adb46`.

`VendiMatrix.source_spectral_row_bound` proves the displayed source trace/row-sum inequality for every real q<1, with all eigenvalue powers explicitly restricted to the positive spectrum. `source_spectral_energy_bound` proves the stronger energy estimate. `source_min_le_row` supplies the minimum-positive-eigenvalue comparison used at order minus infinity. The original VS/LCR normalization is now fully integrated in `formal/VendiScores.lean`, rather than being left as an informal scalar conversion. No claim that the source's already known positive-order theorem was newly proved is made. The weighted-distribution extension above remains a mathematical extension outside these current uniform-score Lean endpoints.


## Original score definitions and minus-infinity endpoint in Lean

`formal/VendiScores.lean` defines the source scores without a full-rank assumption. Its index type has explicit `[Fintype I] [DecidableEq I] [Nonempty I]` instances, so `sizeReal = Fintype.card I` is strictly positive. Its finite-order definitions are exactly

```text
vendiInner = sum over positive eigenvalues of (lambda / N)^q
lcrInner = (1 / N) * sum over rows of (rowSum / N)^(q - 1)
vendiScore = vendiInner^(1 / (1 - q))
lcrScore = lcrInner^(1 / (1 - q))
```

`vendiInner_factor` and `lcrInner_factor` prove the common factor `N^(-q)` explicitly. `source_scores_below_one` instantiates the canonical actual-matrix inequality and monotonicity of the positive outer power; `source_conjecture_negative` specializes this to every real `q < 0`. No spectral decomposition, trace formula, row-energy inequality, or full-rank assumption is supplied to the final endpoint: its only mathematical input is the source matrix hypothesis (real PSD, diagonal one, entries in `[0,1]`).

For order minus infinity, `positiveSpectrum_nonempty` follows from diagonal one and a nonempty index type. `minPositiveEigenvalue` is the actual minimum of the image of the positive canonical eigenvalues, and its strict positivity is proved. `minRowSum` is the actual minimum row sum. `source_conjecture_negativeInfinity` proves `N / minRowSum <= N / minPositiveEigenvalue`, using the canonical matrix minimum theorem. This is the source's negative-infinity formula under its positive-support convention; no formal limit-in-order theorem is claimed. The finite negative orders and this endpoint belong to the same proposed singular-support comparison outcome.

The weighted-distribution extension above is still outside this uniform-score formal development. Existing nonnegative-order results remain prior work and receive no new-discovery credit here.


### Frozen score module and fresh replay

- `formal/VendiScores.lean`: SHA256 `f7ece0ffa805d4b1bb67f8f430cffee57a91442aa9c9e75619a1ef85f9ce84d3`.
- Fresh isolated warning-as-error replay: `build/scores-audit-b_26kbgs/receipt.json`, SHA256 `c38ccee96568fc3dc3bcd87702d3b25e9abeba8a0c55de2a507f8de7fbed4e90`. All three modules rebuilt from source; all 48 local declarations were checked for axiom dependencies, with only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, new axiom, `native_decide`, unsafe declaration, or linter suppression occurs in these three modules.
- Independent core review already passed; independent review of this final score module is requested. The source/prior-art review, final paper and packet remain separate acceptance gates. No new-discovery count is assigned by this working note.
